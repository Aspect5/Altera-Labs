import argparse
import json
import logging
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.progress import Progress
import pandas as pd
from dotenv import load_dotenv
import vertexai
from vertexai.language_models import TextEmbeddingModel
from google.cloud import storage
from neo4j import GraphDatabase


MATHLIB_REPO_URL = os.environ.get(
    "MATHLIB_REPO_URL",
    "https://github.com/leanprover-community/mathlib4.git",
)


class MathlibGraphBuilder:
    """Builds prerequisites for the Mathlib global graph pipeline.

    Implements:
      - Stage 1: Environment setup and source acquisition (clone/pull + lake build)
      - Stage 2: Data extraction via jixia across all Mathlib .lean sources
    """

    def __init__(self, base_dir: Optional[Path] = None) -> None:
        self.base_dir = base_dir or Path(__file__).resolve().parent.parent
        self.pipeline_dir = self.base_dir / "pipelines"
        self.logs_dir = self.base_dir / "logs"
        self.mathlib_src_dir = self.pipeline_dir / "mathlib4_src"
        self.jixia_output_dir = self.pipeline_dir / "jixia_output"
        self.csv_output_dir = self.pipeline_dir / "csv_output"

        self.logs_dir.mkdir(parents=True, exist_ok=True)
        self.pipeline_dir.mkdir(parents=True, exist_ok=True)
        self.jixia_output_dir.mkdir(parents=True, exist_ok=True)
        self.csv_output_dir.mkdir(parents=True, exist_ok=True)
        self._configure_logging()
        # Load .env if present (backend/.env)
        try:
            load_dotenv(self.base_dir / ".env")
        except Exception:  # noqa: BLE001
            pass

    # --- Public orchestration methods -------------------------------------------------
    def run_stage_1_prepare_source(self) -> None:
        """Executes Stage 1: environment setup and source acquisition/build."""
        logging.info("--- Stage 1: Environment setup and source acquisition ---")
        self._clone_or_update_mathlib_repo()
        self._build_mathlib_with_lake()
        logging.info(
            "Stage 1 complete: mathlib4 source is present and successfully built."
        )

    def run_stage_2_extract_data(self) -> Tuple[List[Path], List[Path]]:
        """Executes Stage 2: run jixia on all .lean files to produce JSON outputs.

        Returns:
            Tuple of (decl_json_files, sym_json_files)
        """
        logging.info("--- Stage 2: Extracting data with jixia ---")
        if not shutil.which("jixia"):
            raise RuntimeError(
                "jixia CLI not found in PATH. Please install jixia inside the devcontainer."
            )

        mathlib_root = self.mathlib_src_dir / "Mathlib"
        if not mathlib_root.exists():
            raise RuntimeError(
                f"Mathlib sources not found at {mathlib_root}. Run Stage 1 first."
            )

        lean_files = [p for p in mathlib_root.rglob("*.lean") if p.is_file()]
        if not lean_files:
            raise RuntimeError("No .lean files found under Mathlib/")

        decl_outputs: List[Path] = []
        sym_outputs: List[Path] = []

        with Progress() as progress:
            task_id = progress.add_task("Running jixia on Mathlib .lean files", total=len(lean_files))
            for lean_file in lean_files:
                # Mirror path under jixia_output without the top-level 'Mathlib' directory
                rel = lean_file.relative_to(mathlib_root)
                out_dir = (self.jixia_output_dir / rel.parent).resolve()
                out_dir.mkdir(parents=True, exist_ok=True)

                decl_out = out_dir / f"{rel.stem}.decl.json"
                sym_out = out_dir / f"{rel.stem}.sym.json"

                self._run_command(
                    [
                        "jixia",
                        "-d",
                        str(decl_out),
                        "-s",
                        str(sym_out),
                        str(lean_file),
                    ]
                )

                decl_outputs.append(decl_out)
                sym_outputs.append(sym_out)
                progress.update(task_id, advance=1)

        logging.info(
            f"Stage 2 complete: generated {len(decl_outputs)} decl JSON and {len(sym_outputs)} sym JSON files."
        )
        return decl_outputs, sym_outputs

    def run_stage_3_transform_to_graph(
        self,
        decl_json_files: Optional[List[Path]] = None,
        sym_json_files: Optional[List[Path]] = None,
    ) -> Tuple[pd.DataFrame, pd.DataFrame]:
        """Executes Stage 3: transform jixia JSON outputs into graph CSVs.

        If file lists are not provided, scans the jixia_output directory.
        Returns the constructed nodes and relationships DataFrames.
        """
        logging.info("--- Stage 3: Transforming raw jixia JSON to graph CSVs ---")

        if decl_json_files is None or sym_json_files is None:
            decl_json_files = sorted(self.jixia_output_dir.rglob("*.decl.json"))
            sym_json_files = sorted(self.jixia_output_dir.rglob("*.sym.json"))

        if not decl_json_files:
            raise RuntimeError("No .decl.json files found. Run Stage 2 first.")

        # Map sym files by stem for quick lookup (matching decl file stems)
        sym_by_stem: Dict[str, Path] = {p.stem.replace(".sym", ""): p for p in sym_json_files}

        # Define DataFrame schemas
        node_columns = [
            "fullName",
            "name",
            "kind",
            "signature",
            "docstring",
            "filePath",
            "startLine",
            "startCol",
            "endLine",
            "endCol",
        ]
        rel_columns = ["source_fullName", "target_fullName", "type"]

        nodes: List[Dict] = []
        rels: List[Dict] = []

        mathlib_root = self.mathlib_src_dir / "Mathlib"

        with Progress() as progress:
            task_id = progress.add_task("Parsing jixia JSON and building DataFrames", total=len(decl_json_files))
            for decl_path in decl_json_files:
                stem = decl_path.stem.replace(".decl", "")
                sym_path = sym_by_stem.get(stem)

                # Derive filePath like "Mathlib/....<stem>.lean" from relative jixia path
                rel_dir = decl_path.parent.relative_to(self.jixia_output_dir)
                file_path = str((Path("Mathlib") / rel_dir / f"{stem}.lean").as_posix())

                # Read decl JSON
                try:
                    with open(decl_path, "r", encoding="utf-8") as f:
                        decl_data = json.load(f)
                except Exception as e:  # noqa: BLE001
                    logging.warning(f"Skipping decl JSON {decl_path}: {e}")
                    progress.update(task_id, advance=1)
                    continue

                # Extract declarations into nodes
                for d in _extract_decls_from_decl_json(decl_data, file_path):
                    # Ensure all columns exist
                    node = {k: d.get(k) for k in node_columns}
                    nodes.append(node)

                # Extract dependencies into rels (if sym JSON present)
                if sym_path and sym_path.exists():
                    try:
                        with open(sym_path, "r", encoding="utf-8") as f:
                            sym_data = json.load(f)
                        for s, t in _extract_edges_from_sym_json(sym_data):
                            if s and t:
                                rels.append(
                                    {
                                        "source_fullName": s,
                                        "target_fullName": t,
                                        "type": "DEPENDS_ON",
                                    }
                                )
                    except Exception as e:  # noqa: BLE001
                        logging.warning(f"Skipping sym JSON {sym_path}: {e}")

                progress.update(task_id, advance=1)

        # Build DataFrames
        nodes_df = pd.DataFrame(nodes, columns=node_columns)
        rels_df = pd.DataFrame(rels, columns=rel_columns) if rels else pd.DataFrame(columns=rel_columns)

        # Cleaning and deduplication
        before_nodes = len(nodes_df)
        nodes_df.drop_duplicates(subset=["fullName"], inplace=True)
        after_nodes = len(nodes_df)
        logging.info(f"Nodes deduplicated: {before_nodes} -> {after_nodes}")

        if not rels_df.empty:
            before_rels = len(rels_df)
            # Remove self-loops and duplicate rows
            rels_df = rels_df[rels_df["source_fullName"] != rels_df["target_fullName"]]
            rels_df.drop_duplicates(subset=["source_fullName", "target_fullName", "type"], inplace=True)
            after_rels = len(rels_df)
            logging.info(f"Relationships cleaned: {before_rels} -> {after_rels}")

        # Export to CSV
        nodes_csv = self.csv_output_dir / "mathlib_nodes.csv"
        rels_csv = self.csv_output_dir / "mathlib_rels.csv"
        nodes_df.to_csv(nodes_csv, index=False)
        rels_df.to_csv(rels_csv, index=False)
        logging.info(f"Wrote nodes CSV: {nodes_csv}")
        logging.info(f"Wrote relationships CSV: {rels_csv}")

        return nodes_df, rels_df

    def run_stage_4_generate_embeddings(
        self,
        nodes_df: Optional[pd.DataFrame] = None,
        batch_size: Optional[int] = None,
    ) -> pd.DataFrame:
        """Executes Stage 4: generate vector embeddings with Vertex AI and persist to CSV.

        If nodes_df is not supplied, loads it from csv_output/mathlib_nodes.csv.
        Writes updated CSV (including 'embedding' column) back to csv_output.
        """
        logging.info("--- Stage 4: Generating embeddings with Vertex AI ---")

        # Load data if not supplied
        if nodes_df is None:
            nodes_csv = self.csv_output_dir / "mathlib_nodes.csv"
            if not nodes_csv.exists():
                raise RuntimeError("nodes CSV not found. Run Stage 3 first.")
            nodes_df = pd.read_csv(nodes_csv)

        if nodes_df.empty:
            logging.info("No nodes to embed. Skipping Stage 4.")
            return nodes_df

        # Prepare embedding text
        def build_text(row: pd.Series) -> str:
            name = row.get("name") or ""
            signature = row.get("signature") or ""
            doc = row.get("docstring") or ""
            if pd.isna(name):
                name = ""
            if pd.isna(signature):
                signature = ""
            if pd.isna(doc):
                doc = ""
            return f"{name} : {signature}\n\n{doc}".strip()

        nodes_df["embedding_text"] = nodes_df.apply(build_text, axis=1)

        # Initialize Vertex AI
        project = os.getenv("VERTEX_AI_PROJECT_ID") or os.getenv("GOOGLE_CLOUD_PROJECT")
        location = os.getenv("VERTEX_AI_LOCATION") or os.getenv("GOOGLE_CLOUD_LOCATION") or "us-central1"
        if not project:
            raise RuntimeError(
                "Vertex AI project not configured. Set VERTEX_AI_PROJECT_ID or GOOGLE_CLOUD_PROJECT."
            )
        vertexai.init(project=project, location=location)

        model_name = os.getenv("EMBEDDING_MODEL_NAME", "textembedding-gecko@003")
        model = TextEmbeddingModel.from_pretrained(model_name)

        # Batch embedding
        bs = int(os.getenv("EMBEDDING_BATCH_SIZE", str(batch_size or 250)))
        texts: List[str] = nodes_df["embedding_text"].tolist()
        embeddings: List[List[float]] = []

        with Progress() as progress:
            task_id = progress.add_task("Generating embeddings", total=len(texts))
            for start in range(0, len(texts), bs):
                batch = texts[start : start + bs]
                try:
                    result = model.get_embeddings(
                        batch,
                        task_type="RETRIEVAL_DOCUMENT",
                    )
                    # Each item has .values containing the vector
                    vectors = [e.values for e in result]
                except Exception as e:  # noqa: BLE001
                    logging.error(f"Embedding batch failed at {start}: {e}")
                    # Fallback to empty vectors of length 0
                    vectors = [[] for _ in batch]

                embeddings.extend(vectors)
                progress.update(task_id, advance=len(batch))

        # Attach embeddings and persist
        # Store as JSON array strings for easy LOAD CSV parsing later
        nodes_df["embedding"] = [json.dumps(vec) for vec in embeddings]
        nodes_df.drop(columns=["embedding_text"], inplace=True)

        out_csv = self.csv_output_dir / "mathlib_nodes.csv"
        nodes_df.to_csv(out_csv, index=False)
        logging.info(f"Updated nodes CSV with embeddings: {out_csv}")

        return nodes_df

    def run_stage_5_load_to_neo4j(self) -> None:
        """Executes Stage 5: upload CSVs to GCS and load into Neo4j Aura with LOAD CSV."""
        logging.info("--- Stage 5: Uploading CSVs to GCS and loading into Neo4j ---")

        # Ensure CSVs exist
        nodes_csv = self.csv_output_dir / "mathlib_nodes.csv"
        rels_csv = self.csv_output_dir / "mathlib_rels.csv"
        if not nodes_csv.exists() or not rels_csv.exists():
            raise RuntimeError("CSV outputs not found. Run Stage 3 (and 4 for embeddings) first.")

        # GCS setup
        project = os.getenv("VERTEX_AI_PROJECT_ID") or os.getenv("GOOGLE_CLOUD_PROJECT")
        bucket_name = os.getenv("GCS_BUCKET_NAME")
        if not project or not bucket_name:
            raise RuntimeError("Missing GCP project or GCS bucket. Set GOOGLE_CLOUD_PROJECT and GCS_BUCKET_NAME in backend/.env.")

        gcs_client = storage.Client(project=project)
        bucket = gcs_client.bucket(bucket_name)

        # Upload CSVs
        node_blob_name = f"mathlib_graph/{nodes_csv.name}"
        rel_blob_name = f"mathlib_graph/{rels_csv.name}"
        node_blob = bucket.blob(node_blob_name)
        rel_blob = bucket.blob(rel_blob_name)
        node_blob.cache_control = "public, max-age=3600"
        rel_blob.cache_control = "public, max-age=3600"
        node_blob.upload_from_filename(str(nodes_csv))
        rel_blob.upload_from_filename(str(rels_csv))

        # Make public to allow Neo4j LOAD CSV over HTTPS
        node_blob.make_public()
        rel_blob.make_public()
        nodes_url = node_blob.public_url
        rels_url = rel_blob.public_url
        logging.info(f"Uploaded nodes CSV to: {nodes_url}")
        logging.info(f"Uploaded rels CSV to: {rels_url}")

        # Neo4j setup
        neo4j_uri = os.getenv("NEO4J_URI")
        neo4j_user = os.getenv("NEO4J_USERNAME", "neo4j")
        neo4j_password = os.getenv("NEO4J_PASSWORD")
        if not neo4j_uri or not neo4j_password:
            raise RuntimeError("Missing Neo4j connection env. Set NEO4J_URI, NEO4J_USERNAME, NEO4J_PASSWORD.")

        driver = GraphDatabase.driver(neo4j_uri, auth=(neo4j_user, neo4j_password))

        # Cypher statements
        cypher_wipe = "MATCH (n) DETACH DELETE n"
        cypher_constraint = (
            "CREATE CONSTRAINT declaration_fullName IF NOT EXISTS FOR (d:Declaration) REQUIRE d.fullName IS UNIQUE"
        )
        cypher_load_nodes = f"""
LOAD CSV WITH HEADERS FROM '{nodes_url}' AS row
MERGE (d:Declaration {{fullName: row.fullName}})
ON CREATE SET
 d.name = row.name,
 d.kind = row.kind,
 d.signature = row.signature,
 d.docstring = row.docstring,
 d.filePath = row.filePath,
 d.startLine = toInteger(row.startLine),
 d.startCol = toInteger(row.startCol),
 d.endLine = toInteger(row.endLine),
 d.endCol = toInteger(row.endCol),
 d.embedding = CASE WHEN row.embedding IS NULL OR row.embedding = '' THEN [] ELSE [val IN split(substring(row.embedding, 2, size(row.embedding)-2), ',') | toFloat(val)] END
WITH d, row
CALL apoc.create.addLabels(d, [apoc.text.capitalize(row.kind)]) YIELD node
RETURN count(node)
"""
        cypher_load_rels = f"""
LOAD CSV WITH HEADERS FROM '{rels_url}' AS row
MATCH (source:Declaration {{fullName: row.source_fullName}})
MATCH (target:Declaration {{fullName: row.target_fullName}})
MERGE (source)-[:DEPENDS_ON]->(target)
RETURN count(*)
"""

        # Execute
        with driver.session() as session:
            logging.info("Clearing database and creating constraints...")
            session.run(cypher_wipe)
            session.run(cypher_constraint)
            logging.info("Loading nodes via LOAD CSV...")
            session.run(cypher_load_nodes)
            logging.info("Loading relationships via LOAD CSV...")
            session.run(cypher_load_rels)

        driver.close()
        logging.info("Stage 5 complete: data loaded into Neo4j.")

    def run_stage_6_index_and_cleanup(self) -> None:
        """Executes Stage 6: create vector index and optional cleanup of local/GCS CSVs."""
        logging.info("--- Stage 6: Creating vector index and cleanup ---")

        neo4j_uri = os.getenv("NEO4J_URI")
        neo4j_user = os.getenv("NEO4J_USERNAME", "neo4j")
        neo4j_password = os.getenv("NEO4J_PASSWORD")
        if not neo4j_uri or not neo4j_password:
            raise RuntimeError("Missing Neo4j connection env. Set NEO4J_URI, NEO4J_USERNAME, NEO4J_PASSWORD.")

        vector_dims = int(os.getenv("EMBEDDING_VECTOR_DIM", "768"))
        similarity = os.getenv("EMBEDDING_SIMILARITY", "cosine")

        cypher_vector_index = f"""
CREATE VECTOR INDEX declaration_embedding IF NOT EXISTS
FOR (d:Declaration) ON (d.embedding)
OPTIONS {{indexConfig: {{
  `vector.dimensions`: {vector_dims},
  `vector.similarity_function`: '{similarity}'
}}}}
"""

        driver = GraphDatabase.driver(neo4j_uri, auth=(neo4j_user, neo4j_password))
        with driver.session() as session:
            logging.info("Creating vector index on Declaration.embedding ...")
            session.run(cypher_vector_index)
        driver.close()

        # Optional cleanup
        cleanup = os.getenv("PIPELINE_CLEANUP", "false").lower() == "true"
        if cleanup:
            logging.info("Pipeline cleanup enabled: removing local and GCS CSVs ...")
            # Local cleanup
            nodes_csv = self.csv_output_dir / "mathlib_nodes.csv"
            rels_csv = self.csv_output_dir / "mathlib_rels.csv"
            for p in (nodes_csv, rels_csv):
                try:
                    if p.exists():
                        p.unlink()
                        logging.info(f"Deleted local file: {p}")
                except Exception as e:  # noqa: BLE001
                    logging.warning(f"Failed to delete {p}: {e}")

            # GCS cleanup
            project = os.getenv("VERTEX_AI_PROJECT_ID") or os.getenv("GOOGLE_CLOUD_PROJECT")
            bucket_name = os.getenv("GCS_BUCKET_NAME")
            if project and bucket_name:
                try:
                    gcs_client = storage.Client(project=project)
                    bucket = gcs_client.bucket(bucket_name)
                    for name in ("mathlib_graph/mathlib_nodes.csv", "mathlib_graph/mathlib_rels.csv"):
                        blob = bucket.blob(name)
                        if blob.exists():
                            blob.delete()
                            logging.info(f"Deleted GCS object: gs://{bucket_name}/{name}")
                except Exception as e:  # noqa: BLE001
                    logging.warning(f"Failed to cleanup GCS objects: {e}")

    # --- Internal helpers -------------------------------------------------------------
    def _configure_logging(self) -> None:
        log_file = self.logs_dir / "pipeline.log"

        # Console handler
        console_handler = logging.StreamHandler(sys.stdout)
        console_handler.setLevel(logging.INFO)
        console_handler.setFormatter(
            logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")
        )

        # File handler
        file_handler = logging.FileHandler(log_file)
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(
            logging.Formatter(
                "%(asctime)s [%(levelname)s] %(name)s - %(message)s"
            )
        )

        logging.basicConfig(level=logging.DEBUG, handlers=[console_handler, file_handler])

    def _clone_or_update_mathlib_repo(self) -> None:
        if self.mathlib_src_dir.exists() and (self.mathlib_src_dir / ".git").exists():
            logging.info("mathlib4 repository found. Updating with 'git pull'...")
            self._run_command(["git", "-C", str(self.mathlib_src_dir), "fetch", "--all", "--tags"]) 
            self._run_command(["git", "-C", str(self.mathlib_src_dir), "pull", "--ff-only"]) 
        else:
            logging.info(
                f"Cloning mathlib4 repository into {self.mathlib_src_dir} ..."
            )
            self.mathlib_src_dir.parent.mkdir(parents=True, exist_ok=True)
            self._run_command(["git", "clone", MATHLIB_REPO_URL, str(self.mathlib_src_dir)])

    def _build_mathlib_with_lake(self) -> None:
        lake_path = shutil.which("lake")
        if not lake_path:
            raise RuntimeError(
                "Lake (Lean build tool) not found in PATH. Ensure the devcontainer is used and Lean is installed."
            )

        logging.info("Fetching cached build artifacts: 'lake exe cache get'")
        self._run_command(
            ["lake", "exe", "cache", "get"], cwd=self.mathlib_src_dir
        )

        logging.info("Building mathlib4: 'lake build'")
        self._run_command(["lake", "build"], cwd=self.mathlib_src_dir)

    def _run_command(self, cmd: list[str], cwd: Optional[Path] = None) -> None:
        cwd_str = str(cwd) if cwd else None
        logging.debug(
            f"Running command: {' '.join(cmd)}" + (f" (cwd={cwd_str})" if cwd_str else "")
        )
        process = subprocess.run(
            cmd,
            cwd=cwd_str,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        logging.debug(process.stdout)
        if process.returncode != 0:
            raise RuntimeError(
                f"Command failed with exit code {process.returncode}: {' '.join(cmd)}\n{process.stdout}"
            )


def main() -> int:
    """CLI entry point supporting stages: 1, 2, all."""
    parser = argparse.ArgumentParser(description="Mathlib graph pipeline stages")
    parser.add_argument(
        "--stage",
        choices=["stage1", "stage2", "stage3", "stage4", "stage5", "stage6", "all"],
        default="stage1",
        help="Which stage to run",
    )
    args = parser.parse_args()

    try:
        builder = MathlibGraphBuilder()
        if args.stage == "stage1":
            builder.run_stage_1_prepare_source()
        elif args.stage == "stage2":
            builder.run_stage_2_extract_data()
        elif args.stage == "stage3":
            builder.run_stage_3_transform_to_graph()
        elif args.stage == "stage4":
            builder.run_stage_4_generate_embeddings()
        elif args.stage == "stage5":
            builder.run_stage_5_load_to_neo4j()
        elif args.stage == "stage6":
            builder.run_stage_6_index_and_cleanup()
        else:  # all
            builder.run_stage_1_prepare_source()
            builder.run_stage_2_extract_data()
            builder.run_stage_3_transform_to_graph()
            builder.run_stage_4_generate_embeddings()
            builder.run_stage_5_load_to_neo4j()
            builder.run_stage_6_index_and_cleanup()
        return 0
    except Exception as exc:  # noqa: BLE001
        logging.error(f"Pipeline {args.stage} failed: {exc}")
        return 1


# ---------------------- JSON extraction helpers (defensive) ----------------------

def _extract_decls_from_decl_json(data: object, default_file_path: str) -> List[Dict]:
    """Extract declaration records from jixia decl JSON.

    This function is defensive to accommodate minor schema differences. It expects
    either a list of declaration dicts or a dict with a known key (e.g., "declarations").
    """
    records: List[Dict] = []

    items: List[Dict] = []
    if isinstance(data, list):
        items = [x for x in data if isinstance(x, dict)]
    elif isinstance(data, dict):
        # Common containers
        for key in ("declarations", "decls", "items", "results"):
            v = data.get(key)
            if isinstance(v, list):
                items = [x for x in v if isinstance(x, dict)]
                break

    for item in items:
        full_name = item.get("full_name") or item.get("fullName") or item.get("symbol")
        if not full_name:
            # Some schemas store name under nested fields
            sym = item.get("decl") or item.get("id")
            if isinstance(sym, dict):
                full_name = sym.get("full_name") or sym.get("fullName")
        if not full_name:
            continue

        name = item.get("name") or full_name.split(".")[-1]
        kind = item.get("kind") or item.get("type") or item.get("decl_kind")
        signature = item.get("signature") or item.get("type_string") or item.get("type")
        docstring = item.get("doc_string") or item.get("docstring") or item.get("doc")

        # Range handling
        start_line = start_col = end_line = end_col = None
        rng = item.get("range") or item.get("pos")
        if isinstance(rng, dict):
            # Common keys in Lean tooling
            start = rng.get("start") or rng.get("start_pos") or {}
            end = rng.get("end") or rng.get("end_pos") or {}
            start_line = start.get("line") or start.get("lineNumber")
            start_col = start.get("column") or start.get("col")
            end_line = end.get("line") or end.get("lineNumber")
            end_col = end.get("column") or end.get("col")

        records.append(
            {
                "fullName": full_name,
                "name": name,
                "kind": kind,
                "signature": signature,
                "docstring": docstring,
                "filePath": default_file_path,
                "startLine": start_line,
                "startCol": start_col,
                "endLine": end_line,
                "endCol": end_col,
            }
        )

    return records


def _extract_edges_from_sym_json(data: object) -> List[Tuple[str, str]]:
    """Extract dependency edges (source_fullName, target_fullName) from jixia sym JSON.

    This function is defensive to accommodate schema differences. It tries several
    common shapes for a reference graph output.
    """
    edges: List[Tuple[str, str]] = []

    def _add_edge(src: Optional[str], tgt: Optional[str]) -> None:
        if src and tgt:
            edges.append((src, tgt))

    if isinstance(data, list):
        # A list of references for a single source declaration
        for item in data:
            if isinstance(item, dict):
                src = item.get("source") or item.get("from") or item.get("full_name")
                refs = item.get("references") or item.get("deps") or item.get("to")
                if isinstance(refs, list):
                    for ref in refs:
                        if isinstance(ref, dict):
                            tgt = ref.get("full_name") or ref.get("target") or ref.get("to")
                            _add_edge(src, tgt)
                        elif isinstance(ref, str):
                            _add_edge(src, ref)
                elif isinstance(refs, dict):
                    tgt = refs.get("full_name") or refs.get("target")
                    _add_edge(src, tgt)
    elif isinstance(data, dict):
        # Possible top-level containers
        for key in ("references", "edges", "deps", "results", "items"):
            seq = data.get(key)
            if isinstance(seq, list):
                for item in seq:
                    if not isinstance(item, dict):
                        continue
                    src = item.get("source") or item.get("from") or item.get("full_name")
                    targets = item.get("targets") or item.get("references") or item.get("deps") or item.get("to")
                    if isinstance(targets, list):
                        for ref in targets:
                            if isinstance(ref, dict):
                                tgt = ref.get("full_name") or ref.get("target") or ref.get("to")
                                _add_edge(src, tgt)
                            elif isinstance(ref, str):
                                _add_edge(src, ref)
                    elif isinstance(targets, dict):
                        tgt = targets.get("full_name") or targets.get("target")
                        _add_edge(src, tgt)

    return edges


if __name__ == "__main__":
    sys.exit(main())


