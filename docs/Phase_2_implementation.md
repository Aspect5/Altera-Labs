Altera Labs Project: Implementation Plan for Phase 2 Offline Global Graph Construction




Executive Summary


This document presents a comprehensive, actionable implementation plan for Phase 2 of the Altera Labs project: the offline construction of a global knowledge graph from the Lean 4 mathlib4 library. The current data architecture, characterized by fragmented, untyped data stores (classes.json, lean_knowledge_base.py), is insufficient to support the project's long-term vision of a "Community-Partitioned GraphRAG index." This plan details the design and execution of a robust, automated data engineering pipeline to supersede these legacy models, establishing a unified and semantically rich data foundation.
The proposed solution is an end-to-end Extract, Transform, and Load (ETL) pipeline, designed to operate as a standalone, offline process within the project's existing devcontainer environment. The pipeline's core stages are as follows: First, it will systematically parse the entire mathlib4 source code using the jixia static analysis tool, chosen for its unique ability to extract a post-elaboration "reference graph" that captures true semantic dependencies between mathematical declarations. Second, this raw data will be transformed into a typed property graph model, meticulously designed to represent both the logical dependency structure and the physical organization of the library. During this stage, vector embeddings for declaration docstrings and signatures will be generated using the project's configured Google Cloud Vertex AI services. Finally, the transformed data, formatted as CSV files, will be staged in a Google Cloud Storage bucket and bulk-loaded into the target Neo4j Aura database using the highly performant and scalable LOAD CSV command.
This initiative will deliver a "single source of truth" for the mathematical knowledge contained within mathlib4, stored in a high-performance graph database optimized for complex queries and semantic search. It eliminates significant technical debt, provides a scalable data infrastructure, and directly enables the development of the advanced GraphRAG capabilities that are central to the Altera Labs mission. The successful execution of this plan will mark a critical transition from a prototype-level data model to a production-ready knowledge graph architecture.


Recommended Toolchain


The selection of an appropriate toolchain is paramount to the success, efficiency, and maintainability of the data ingestion pipeline. The following tools and libraries are recommended based on a thorough evaluation of their capabilities, compatibility with the existing project environment, and alignment with industry best practices for large-scale data engineering.


Lean 4 Parsing and Analysis


The most critical component of the pipeline is the tool used to parse .lean source files. The primary requirement is the ability to extract not just the declarations themselves, but their fully resolved, semantic dependencies.
* Primary Tool: jixia
   * Justification: jixia is a static analysis tool engineered specifically for Lean 4. Its decisive advantage over other parsers is the "Symbol" plugin, which explicitly generates a "reference graph" after the Lean elaboration process has completed.1 Elaboration is the phase where Lean resolves names, infers types, and makes implicit arguments explicit, turning surface-level syntax into a fully specified internal representation.2 By operating post-elaboration,
jixia provides a dependency graph that reflects the true logical connections between fully qualified declarations, which is precisely the information required to build a high-fidelity knowledge graph. This capability is validated by its use in advanced research projects for dependency analysis.3 Furthermore, its non-intrusive design respects the
mathlib4 build cache, which significantly accelerates repeated analysis runs.1
   * Alternatives Considered and Rejected:
   * LeanDojo: This is a powerful toolset that produces highly detailed trace.xml files containing resolved dependency information, including the definitive file path (def_path) for each identifier.4 While capable, the direct JSON output from
jixia's reference graph plugin presents a more straightforward data structure for our transformation logic, reducing the complexity of the parsing and data framing stage.
   * ast_export: This tool was rejected because it provides only a raw Abstract Syntax Tree (AST) of the source code.5 An AST represents the syntactic structure but does not contain the semantic, post-elaboration information about resolved dependencies. Using its output would necessitate building a complex and fragile secondary analysis layer to resolve names and infer connections, effectively re-implementing a significant portion of the Lean elaborator.6
   * lean4export: This tool, a successor to a Lean 3 utility, produces a custom, non-standard text format.7 Integrating this would require the development and maintenance of a bespoke parser. The prevailing expert opinion within the Lean community favors standardization on common interchange formats like JSON, rendering this approach undesirable from a maintainability perspective.8


Data Transformation and Orchestration (Python)


The pipeline's orchestration, data manipulation, and interaction with external services will be managed by a Python script, leveraging a set of standard, high-performance libraries.
      * pandas: The cornerstone of the transformation stage. It provides powerful and memory-efficient DataFrame structures, which are ideal for ingesting the numerous JSON files produced by jixia, cleaning and reshaping the data, and exporting it to the flat, tabular CSV format required by Neo4j's bulk loader.
      * google-cloud-aiplatform: The official Google Cloud SDK for Python. This library will be used to interface directly with Vertex AI services to generate text embeddings for declaration docstrings and signatures, a core requirement for enabling future semantic search capabilities.9
      * google-cloud-storage: The official SDK for programmatically interacting with Google Cloud Storage (GCS). Its role in the pipeline is to upload the generated node and relationship CSV files to a designated GCS bucket, staging them for ingestion by Neo4j Aura.
      * neo4j: The official Python driver for Neo4j. This driver will be used to manage the connection to the Neo4j Aura instance, execute preparatory Cypher commands (e.g., clearing the database, creating schema constraints), trigger the LOAD CSV ingestion process, and apply post-load optimizations like creating indexes.11
      * python-dotenv: A utility for managing environment variables. It allows sensitive credentials (Neo4j password, GCP keys) and configuration parameters to be stored in a .env file, which is excluded from source control, adhering to security best practices.
      * rich: A library for creating rich text and beautiful formatting in the terminal. It will be used to provide a superior developer experience during pipeline execution, with color-coded logging, progress bars, and cleanly formatted status updates.


Summary of Recommended Libraries and Tools


The following table provides a consolidated view of the recommended software stack for the pipeline.


Category
	Tool/Library
	Version (Recommended)
	Purpose in Pipeline
	Justification
	Lean Parsing
	jixia
	Latest
	Extracts declarations, docstrings, and a post-elaboration "reference graph" from .lean files into JSON.
	Provides essential semantic dependency data unavailable in simpler AST parsers.1
	Data Manipulation
	pandas
	2.x
	Structures raw JSON data into Node and Relationship dataframes for transformation and CSV export.
	Industry standard for efficient, large-scale data manipulation in Python.13
	Cloud Storage Interface
	google-cloud-storage
	Latest
	Uploads the generated Node and Relationship CSV files to a Google Cloud Storage bucket for staging.
	Official, robust SDK for interacting with GCS, required for the LOAD CSV strategy.14
	AI/Embedding Interface
	google-cloud-aiplatform
	Latest
	Submits text (docstrings, signatures) to Vertex AI to generate vector embeddings.
	Official SDK for leveraging the project's existing Vertex AI environment.10
	Graph Database Interface
	neo4j
	5.x
	Executes Cypher commands against Neo4j Aura for schema setup, data loading (LOAD CSV), and indexing.
	Official driver for all database management and query operations.11
	Configuration Management
	python-dotenv
	Latest
	Loads secrets and configuration from a .env file into the pipeline's environment.
	Standard practice for secure management of credentials and configuration.
	Logging/CLI Interface
	rich
	Latest
	Provides formatted, colorized logging and progress bars to the console for improved usability.
	Enhances developer experience and pipeline observability.
	

Proposed Graph Schema and API Transformation


The design of the graph schema is the most critical architectural decision in this project. The proposed model is engineered to be semantically rich, query-efficient, and capable of supporting both the immediate needs of the application and the long-term vision of a partitioned RAG index. It explicitly unifies and supersedes the disparate data models currently in use.


A. Neo4j Graph Data Model for Mathlib


The model is a labeled property graph that captures two fundamental aspects of the mathlib4 library simultaneously: the logical dependency graph (how theorems and definitions rely on each other) and the physical/organizational graph (how these declarations are grouped into files and namespaces). This dual structure is a powerful feature that enables complex queries bridging both domains.


Node Labels


Node labels are used to categorize entities within the graph, analogous to types or classes.
      * :Declaration: An abstract base label applied to all top-level Lean declarations (theorem, def, axiom, etc.). This allows for high-level queries that operate on any type of declaration, such as "Find all declarations in this file."
      * :Theorem, :Lemma, :Definition, :Axiom, :Structure, :Inductive: These are concrete labels that inherit from :Declaration. Each node of a specific kind will have both the :Declaration label and its specific type label (e.g., a theorem node will have labels :Declaration:Theorem). This maps directly to Lean's declaration keywords 17 and enables highly specific queries (e.g., "Find all
:Theorem nodes that :DEPENDS_ON a specific :Definition").
      * :Module: Represents a single .lean source file. This node type is essential for understanding the physical file structure of the library and for queries related to file-level imports and organization.
      * :Namespace: Represents a logical Lean namespace (e.g., Mathlib.Data.Nat). Namespaces can span multiple files and provide a crucial logical grouping mechanism that is distinct from the file structure. Modeling this explicitly is key to enabling future community-based partitioning.


Node Properties


Properties store the detailed attributes of each node.
         * fullName (string, unique): The fully qualified, unique name of the declaration (e.g., Mathlib.Data.Nat.Basic.add_comm). This serves as the primary identifier for each declaration node and will have a uniqueness constraint applied in the database for data integrity and performance.
         * name (string): The short, local name of the declaration (e.g., add_comm).
         * kind (string): The declaration type, matching the concrete label (e.g., 'theorem', 'def'). This property facilitates filtering and is useful for populating the frontend.
         * signature (string): The full type signature of the declaration (e.g., ∀ (n m : ℕ), n + m = m + n).
         * docstring (string): The complete docstring associated with the declaration, if one exists. This text is a primary candidate for vector embedding.
         * filePath (string): The relative path to the source .lean file where the declaration is defined (e.g., Mathlib/Data/Nat/Basic.lean).
         * startLine, startCol, endLine, endCol (integer): The precise source code location, enabling direct links from the application back to the source code on GitHub.
         * embedding (list of floats): The vector embedding generated by Vertex AI. This property will be stored as a list of floating-point numbers and will be indexed using Neo4j's native vector index for efficient similarity search.18


Relationship Types


Relationships define the directed connections between nodes, forming the structure of the graph.
         * d1:Declaration --> d2:Declaration: This is the core relationship of the logical graph. It represents a directed edge from a declaration d1 to a declaration d2 that it uses in its definition or proof.
         * d:Declaration --> m:Module: This relationship connects a declaration to the single :Module (file) in which it is physically defined.
         * d:Declaration --> n:Namespace: This connects a declaration to the logical :Namespace it belongs to.
         * m1:Module --> m2:Module: This represents the import statements at the top of a Lean file, creating a file-level dependency graph.


Schema Summary Tables


The following tables provide a formal specification of the proposed graph schema.
Table: Node Labels and Properties
Label
	Inherits From
	Description
	Properties (name: type [constraints])
	:Declaration
	-
	Abstract base label for any Lean declaration.
	fullName: string [unique], name: string, kind: string, signature: string, docstring: string, filePath: string, startLine: int, startCol: int, endLine: int, endCol: int, embedding: list<float> [vector index]
	:Theorem, :Lemma, etc.
	:Declaration
	Concrete type of a Lean declaration.
	(Inherits all properties from :Declaration)
	:Module
	-
	Represents a single .lean source file.
	filePath: string [unique], name: string
	:Namespace
	-
	Represents a logical Lean namespace.
	fullName: string [unique], name: string
	Table: Relationship Types
Source Label
	Relationship Type
	Target Label
	Description
	:Declaration
	:DEPENDS_ON
	:Declaration
	The source declaration's definition or proof references the target declaration.
	:Declaration
	:DEFINED_IN
	:Module
	The declaration is physically located in the target source file.
	:Declaration
	:PART_OF
	:Namespace
	The declaration belongs to the target logical namespace.
	:Module
	:IMPORTS
	:Module
	The source file imports the target file.
	

B. API Transformation Logic


A key project constraint is to maintain the existing frontend API contract, which expects a simple, untyped graph structure. The richness of the new Neo4j model can be seamlessly mapped to this structure at query time, creating a "view" of the data that decouples the backend storage model from the frontend presentation model. This is a significant architectural advantage, as it allows the graph model to evolve independently without requiring changes to the frontend client.
The transformation is achieved with a Cypher query that projects the complex graph into the required JSON format.


Conceptual Cypher Query for API Compatibility


The following query demonstrates how to retrieve a local subgraph around a specific declaration (e.g., a theorem selected by the user) and format it for the KnowledgeGraph.tsx component.


Cypher




// This query is executed with a parameter, e.g., $startNodeFullName,
// which contains the unique name of the declaration to start the graph from.
// Example: $startNodeFullName = "Mathlib.Data.Nat.Basic.add_comm"

// 1. Find all paths of dependencies up to 2 hops away from the starting node.
// The direction is reversed (`<-`) because we want to find what the start node *depends on*.
MATCH path = (startNode:Declaration {fullName: $startNodeFullName})<--(dependency:Declaration)

// 2. Collect all unique nodes from these paths into a single list.
WITH nodes(path) AS path_nodes
UNWIND path_nodes AS node
WITH COLLECT(DISTINCT node) AS unique_nodes

// 3. Project the collected nodes into the format required by the frontend API.
// The 'id' becomes the unique fullName, and 'label' is the short name.
// Additional properties like 'kind' can be passed for richer frontend rendering.
WITH [n IN unique_nodes | {
   id: n.fullName,
   label: n.name,
   type: n.kind
}] AS output_nodes, unique_nodes

// 4. Find all DEPENDS_ON relationships that exist *between the nodes in our collected subgraph*.
// This prevents pulling in edges that lead outside the desired 2-hop view.
MATCH (source:Declaration)-->(target:Declaration)
WHERE source IN unique_nodes AND target IN unique_nodes

// 5. Project these relationships into the required edge format.
WITH output_nodes, COLLECT({
   source: source.fullName,
   target: target.fullName,
   weight: 1.0 // A placeholder weight; can be customized later.
}) AS output_edges

// 6. Return the final, fully-formed JSON object that matches the API contract.
RETURN {
   nodes: output_nodes,
   edges: output_edges,
   knowledgeState: {
       // This can be populated with metadata about the graph state in the future.
       startNode: $startNodeFullName,
       depth: 2
   }
} AS graphData

This query effectively acts as a translation layer within the database itself. The Python backend's responsibility is reduced to executing this query with the appropriate parameter and forwarding the resulting JSON object, which is already in the correct format, directly to the frontend. This approach is highly efficient, minimizing data transfer and processing logic within the application layer.


Detailed Pipeline Implementation Plan


This section provides a granular, step-by-step procedure for the offline data ingestion pipeline. The process is designed as a sequence of distinct, automatable stages, from source code acquisition to final database indexing.


Stage 1: Environment Setup and Source Acquisition


This initial stage prepares the local environment and ensures the mathlib4 source code is present and correctly built.
         * Step 1.1: Acquire mathlib4 Source Code: The pipeline script will first check for the existence of a local mathlib4 repository clone (e.g., within backend/pipelines/mathlib4_src).
         * If the directory does not exist, the script will execute git clone https://github.com/leanprover-community/mathlib4.git to download the repository.
         * If the directory exists, it will execute git pull to update the code to the latest version, ensuring the graph is always built from the most recent state of the library.19
         * Step 1.2: Build mathlib4 Dependencies: Static analysis of Lean code requires the compiled .olean files, which contain metadata produced by the Lean compiler. The script will trigger the build process using Python's subprocess module.
         * Change the working directory to the mathlib4 repository.
         * Execute lake exe cache get. This command downloads pre-compiled build artifacts, dramatically speeding up the build process by avoiding a full compilation from scratch.19
         * Execute lake build. This command compiles any remaining files and ensures the entire project is in a valid state for analysis.21 The pipeline will check for successful exit codes from these commands before proceeding.


Stage 2: Data Extraction via jixia


With the source code prepared, this stage systematically runs the jixia static analyzer across the entire library to extract the raw data.
         * Step 2.1: Identify Target Files: The script will perform a recursive file system scan of the mathlib4/Mathlib directory to generate a list of all .lean files to be processed.
         * Step 2.2: Execute jixia Analysis: The script will iterate through the list of target files. For each file, it will construct and execute a jixia command-line call.
         * The command will be structured as: jixia -d <output_decl.json> -s <output_sym.json> <input_file.lean>. This enables the Declaration plugin (for source-level info like docstrings and signatures) and the critical Symbol plugin (for the post-elaboration reference graph).1
         * The output JSON files will be saved to a temporary directory (e.g., backend/pipelines/jixia_output/), mirroring the mathlib4 directory structure to maintain context (e.g., .../jixia_output/Data/Nat/Basic.decl.json).
         * Step 2.3: Aggregate Output Paths: The script will collect the file paths of all generated .decl.json and .sym.json files. This process will be monitored with a rich progress bar, as analyzing thousands of files will be the most time-consuming step of the extraction phase.


Stage 3: Transformation to Graph CSVs


This stage is the core of the ETL logic, converting the raw, nested JSON output from jixia into two clean, tabular CSV files that map directly to the Neo4j graph schema.
         * Step 3.1: Initialize DataFrames: Two empty Pandas DataFrames will be created: nodes_df and rels_df. The columns of these DataFrames will precisely match the node and relationship properties defined in the schema (e.g., fullName, name, docstring, filePath, source_fullName, target_fullName).
         * Step 3.2: Process and Transform jixia Outputs: The script will iterate through the aggregated list of jixia JSON files. For each file pair (.decl.json and .sym.json):
         * It will parse the JSON content.
         * For each entry in the Declaration and Symbol outputs, it will extract the relevant fields.
         * A new row will be appended to nodes_df for each unique declaration, mapping jixia fields (full_name, name, doc_string, range, type) to the DataFrame columns (fullName, name, docstring, startLine, signature, etc.).
         * For each dependency identified in the Symbol plugin's reference graph, a new row will be appended to rels_df, populating the source_fullName and target_fullName columns, with the relationship type set to DEPENDS_ON.
         * Step 3.3: Data Cleaning and Deduplication: After processing all files, a final cleaning pass will be performed on the DataFrames. This includes dropping any duplicate rows from nodes_df based on the fullName column to ensure entity uniqueness, and removing any self-referential loops from rels_df.


Stage 4: Embedding Generation with Vertex AI


This stage enriches the node data with semantic vector representations.
         * Step 4.1: Prepare Text for Embedding: A new column, embedding_text, will be created in nodes_df. For each declaration, this column will contain a concatenated string of its most meaningful textual content, such as f"{row['name']} : {row['signature']}\n\n{row['docstring']}". This provides richer context to the embedding model.
         * Step 4.2: Initialize Vertex AI Client: The script will initialize the Vertex AI client using vertexai.init() and instantiate the text embedding model: model = TextEmbeddingModel.from_pretrained("textembedding-gecko@003").9
         * Step 4.3: Batch and Generate Embeddings: The embedding_text column will be processed in batches to comply with API rate limits (e.g., batches of 250 texts).10 For each batch, the script will call
model.get_embeddings(), specifying task_type='RETRIEVAL_DOCUMENT' to optimize the embeddings for downstream RAG tasks.9
         * Step 4.4: Store Embeddings: The resulting list of embedding vectors will be assigned back to a new embedding column in the nodes_df.


Stage 5: Staging and Bulk Loading into Neo4j Aura


This stage efficiently loads the prepared data into the cloud database using a performance-optimized strategy.
            * Step 5.1: Export to CSV: The final nodes_df and rels_df DataFrames will be exported to local CSV files (e.g., mathlib_nodes.csv, mathlib_rels.csv) in a temporary directory.
            * Step 5.2: Upload to Google Cloud Storage: The script will use the google-cloud-storage SDK to upload these two CSV files to a pre-configured GCS bucket specified in the .env file.
            * Step 5.3: Connect to Neo4j Aura: The script will instantiate the Neo4j Python driver using the credentials from the .env file.
            * Step 5.4: Prepare Database: A series of pre-flight Cypher commands will be executed in a transaction to ensure the import is idempotent:
            * MATCH (n) DETACH DELETE n;: Wipes all existing data from the database.
            * CREATE CONSTRAINT declaration_fullName IF NOT EXISTS FOR (d:Declaration) REQUIRE d.fullName IS UNIQUE;: Creates the uniqueness constraint before loading. While indexes are typically created after, a uniqueness constraint helps MERGE performance during the load itself.23
            * Step 5.5: Execute LOAD CSV: The core data loading will be performed using the LOAD CSV command. This method is significantly faster for large datasets than sending individual CREATE statements programmatically.23 The command will point to the public HTTPS URL of the CSV file in the GCS bucket.
            * Node Import Query:
Cypher
LOAD CSV WITH HEADERS FROM 'GCS_URL_FOR_NODES.csv' AS row
// Use MERGE to leverage the uniqueness constraint
MERGE (d:Declaration {fullName: row.fullName})
// Set properties on creation
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
 d.embedding = [val IN split(substring(row.embedding, 1, size(row.embedding)-2), ',') | toFloat(val)]
// Dynamically add the specific label (e.g., :Theorem)
WITH d, row
CALL apoc.create.addLabels(d, [apoc.text.capitalize(row.kind)]) YIELD node
RETURN count(node)

            * Relationship Import Query:
Cypher
LOAD CSV WITH HEADERS FROM 'GCS_URL_FOR_RELS.csv' AS row
MATCH (source:Declaration {fullName: row.source_fullName})
MATCH (target:Declaration {fullName: row.target_fullName})
MERGE (source)-->(target)
RETURN count(*)



Stage 6: Post-Load Indexing and Cleanup


The final stage applies performance optimizations and cleans up temporary artifacts.
               * Step 6.1: Create Vector Index: After all data is loaded, the vector index is created. This is done post-load because modifying an indexed property during a bulk load can slow down the import process.
Cypher
CREATE VECTOR INDEX declaration_embedding IF NOT EXISTS
FOR (d:Declaration) ON (d.embedding)
OPTIONS {indexConfig: {
 `vector.dimensions`: 768, // Dimension of textembedding-gecko
 `vector.similarity_function`: 'cosine'
}}

12
               * Step 6.2: Create Supporting Indexes: Additional indexes on frequently queried properties can be created here (e.g., on :Module(filePath)).
               * Step 6.3: Cleanup: The script will delete the local CSV files and the corresponding objects from the GCS bucket to avoid unnecessary storage costs and artifacts.


Configuration and Logging


                  * Configuration: A .env file located in the backend/ directory will manage all necessary secrets and configuration variables. This file should be added to .gitignore.
Code snippet
# Neo4j Aura Credentials
NEO4J_URI="neo4j+s://<instance-id>.databases.neo4j.io"
NEO4J_USERNAME="neo4j"
NEO4J_PASSWORD="<your-aura-password>"

# Google Cloud Configuration
GCP_PROJECT_ID="<your-gcp-project-id>"
GCS_BUCKET_NAME="altera-labs-mathlib-graph-staging"

                  * Logging: The Python logging module will be configured at the start of the script. It will use two handlers:
                     1. A rich.logging.RichHandler to output colorized, easy-to-read logs to the console (stdout). This handler will be set to the INFO level.
                     2. A logging.FileHandler to write comprehensive, timestamped logs to a persistent file at backend/logs/pipeline.log. This handler will be set to the DEBUG level to capture granular detail for troubleshooting.


Conceptual Python Code Blueprint (backend/pipelines/build_mathlib_graph.py)


The following Python script blueprint provides a structural foundation for the pipeline implementation. It outlines the main classes, methods, and the orchestration logic that connects the stages described in the implementation plan. This code is intended as a high-level scaffold for the development team.


Python




# backend/pipelines/build_mathlib_graph.py

import logging
import os
import subprocess
import json
from pathlib import Path
from typing import List, Tuple

import pandas as pd
from google.cloud import aiplatform, storage
from neo4j import GraphDatabase, Driver
from rich.logging import RichHandler
from rich.progress import Progress
from dotenv import load_dotenv

# --- Constants ---
MATHLIB_REPO_URL = "https://github.com/leanprover-community/mathlib4.git"
BASE_DIR = Path(__file__).parent.parent
PIPELINE_DIR = BASE_DIR / "pipelines"
LOG_DIR = BASE_DIR / "logs"
MATHLIB_SRC_DIR = PIPELINE_DIR / "mathlib4_src"
JIXIA_OUTPUT_DIR = PIPELINE_DIR / "jixia_output"
CSV_OUTPUT_DIR = PIPELINE_DIR / "csv_output"

# --- Logging and Configuration Setup ---
LOG_DIR.mkdir(exist_ok=True)
logging.basicConfig(
   level=logging.INFO,
   format="%(asctime)s [%(levelname)s] %(message)s",
   handlers=
)
load_dotenv(BASE_DIR / ".env")

class MathlibGraphBuilder:
   """Orchestrates the end-to-end pipeline for building the Mathlib graph."""

   def __init__(self):
       # Load configuration from environment variables
       self.neo4j_uri = os.getenv("NEO4J_URI")
       self.neo4j_user = os.getenv("NEO4J_USERNAME")
       self.neo4j_password = os.getenv("NEO4J_PASSWORD")
       self.gcp_project = os.getenv("GCP_PROJECT_ID")
       self.gcs_bucket_name = os.getenv("GCS_BUCKET_NAME")
       self.neo4j_driver = None
       self.gcs_client = None

   def _connect_services(self):
       """Initializes connections to Neo4j and GCS."""
       logging.info("Connecting to Neo4j and Google Cloud services...")
       self.neo4j_driver = GraphDatabase.driver(self.neo4j_uri, auth=(self.neo4j_user, self.neo4j_password))
       self.gcs_client = storage.Client(project=self.gcp_project)
       aiplatform.init(project=self.gcp_project, location="us-central1")

   def _close_connections(self):
       """Closes any open service connections."""
       if self.neo4j_driver:
           self.neo4j_driver.close()
           logging.info("Neo4j connection closed.")

   def run_pipeline(self):
       """Executes the entire ETL pipeline in sequence."""
       try:
           self._connect_services()
           self._stage_1_prepare_source()
           jixia_files = self._stage_2_extract_data()
           nodes_df, rels_df = self._stage_3_transform_to_graph(jixia_files)
           nodes_with_embeddings_df = self._stage_4_generate_embeddings(nodes_df)
           self._stage_5_and_6_load_and_index_graph(nodes_with_embeddings_df, rels_df)
           logging.info("✅ Pipeline completed successfully.")
       except Exception as e:
           logging.error(f"Pipeline failed: {e}", exc_info=True)
       finally:
           self._close_connections()

   def _stage_1_prepare_source(self):
       """Clones/pulls mathlib4 and runs 'lake build'."""
       logging.info("--- Stage 1: Preparing mathlib4 source ---")
       # Implementation for git clone/pull and subprocess calls to lake
       #...
       logging.info("Mathlib4 source is up-to-date and built.")

   def _stage_2_extract_data(self) -> List[Path]:
       """Runs jixia on all.lean files and returns paths to JSON outputs."""
       logging.info("--- Stage 2: Extracting data with jixia ---")
       # Implementation to find.lean files and run jixia
       # Use rich.progress to show progress
       #...
       logging.info(f"Extraction complete. Found {len(jixia_files)} jixia output files.")
       return # Return list of file paths

   def _stage_3_transform_to_graph(self, json_files: List[Path]) -> Tuple:
       """Parses jixia JSONs and transforms them into node and relationship DataFrames."""
       logging.info("--- Stage 3: Transforming raw data to graph format ---")
       # Core transformation logic using pandas to build nodes_df and rels_df
       #...
       logging.info(f"Transformation complete. Generated {len(nodes_df)} nodes and {len(rels_df)} relationships.")
       return pd.DataFrame(), pd.DataFrame()

   def _stage_4_generate_embeddings(self, nodes_df: pd.DataFrame) -> pd.DataFrame:
       """Generates vector embeddings for node content using Vertex AI."""
       logging.info("--- Stage 4: Generating embeddings with Vertex AI ---")
       # Implementation to batch texts and call Vertex AI SDK
       #...
       logging.info("Embedding generation complete.")
       return nodes_df

   def _stage_5_and_6_load_and_index_graph(self, nodes_df: pd.DataFrame, rels_df: pd.DataFrame):
       """Uploads CSVs to GCS, runs LOAD CSV, and creates indexes in Neo4j."""
       logging.info("--- Stage 5 & 6: Loading data to Neo4j and indexing ---")
       # 1. Export DataFrames to local CSV files
       # 2. Upload CSVs to GCS bucket
       # 3. Execute Cypher queries for cleanup, LOAD CSV, and index creation
       # 4. Cleanup local and GCS files
       #...
       logging.info("Data loading and indexing complete.")

def main():
   """CLI entry point for the pipeline."""
   builder = MathlibGraphBuilder()
   builder.run_pipeline()

if __name__ == "__main__":
   main()

This blueprint establishes a clean, class-based structure that encapsulates the pipeline's logic. Each stage is a distinct method, promoting modularity and testability. The main function serves as the entry point, which will be registered in pyproject.toml to create the command-line executable.


Integration Plan


The final step is to integrate this new data pipeline and its resulting Neo4j graph into the existing Altera Labs project. This involves modifying the backend API to query Neo4j instead of local files and providing a simple command for developers to execute the pipeline.


A. Backend API Modifications (backend/app.py)


The backend Flask application must be updated to treat Neo4j as its primary data source for graph information. The functions that currently read from data/classes.json and backend/lean_knowledge_base.py will be refactored.
                     * Connection Management: A single, global Neo4j driver instance should be initialized when the Flask application starts. This instance is thread-safe and manages a connection pool, making it efficient to reuse across multiple requests.
Python
# In backend/app.py or a new backend/db.py module
from neo4j import GraphDatabase
import os

def get_neo4j_driver():
   # This function can use Flask's application context (g) to store
   # and reuse the driver instance across a request's lifetime.
   uri = os.getenv("NEO4J_URI")
   user = os.getenv("NEO4J_USERNAME")
   password = os.getenv("NEO4J_PASSWORD")
   return GraphDatabase.driver(uri, auth=(user, password))

# Initialize the driver when the app starts
driver = get_neo4j_driver()

                     * Route Refactoring: Routes that serve graph data, such as /api/dashboard/class/<class_id>, must be modified to query Neo4j.
                        * Before (Conceptual):
Python
# @app.route('/api/dashboard/class/<class_id>')
# def get_class_graph(class_id):
#     with open('data/classes.json') as f:
#         data = json.load(f)
#     #... complex logic to filter nodes and edges for class_id...
#     return jsonify(subgraph)

                        * After (Implementation):
Python
from flask import jsonify

# A constant holding the API transformation query
API_GRAPH_QUERY = """
MATCH path = (startNode:Declaration {fullName: $startNodeFullName})<--(dependency:Declaration)
WITH nodes(path) AS path_nodes
UNWIND path_nodes AS node
WITH COLLECT(DISTINCT node) AS unique_nodes
WITH [n IN unique_nodes | {id: n.fullName, label: n.name, type: n.kind}] AS output_nodes, unique_nodes
MATCH (source:Declaration)-->(target:Declaration)
WHERE source IN unique_nodes AND target IN unique_nodes
WITH output_nodes, COLLECT({source: source.fullName, target: target.fullName, weight: 1.0}) AS output_edges
RETURN {nodes: output_nodes, edges: output_edges, knowledgeState: {}} AS graphData
"""

@app.route('/api/dashboard/class/<path:class_id>')
def get_class_graph(class_id):
   try:
       with driver.session() as session:
           result = session.run(API_GRAPH_QUERY, startNodeFullName=class_id)
           graph_data = result.single()
           if not graph_data['nodes']:
               return jsonify({"error": "Declaration not found"}), 404
           return jsonify(graph_data)
   except Exception as e:
       logging.error(f"Error querying Neo4j for {class_id}: {e}")
       return jsonify({"error": "Internal server error"}), 500



B. Pipeline Execution Command (scripts/manage.sh)


To ensure a seamless and reproducible developer workflow, a new command will be added to the project's management script, scripts/manage.sh. This provides a simple, high-level interface to trigger the entire offline pipeline.
                           * pyproject.toml Configuration: First, the Python script must be registered as an executable command in the project's pyproject.toml file.
Ini, TOML
# In pyproject.toml
[project.scripts]
build-mathlib-graph = "backend.pipelines.build_mathlib_graph:main"

When the project is installed in editable mode (pip install -e.) within the devcontainer, this configuration creates an executable named build-mathlib-graph in the virtual environment's path.
                           * manage.sh Implementation: A new function and case statement will be added to the script.
Bash
#!/bin/bash
# scripts/manage.sh

#... (other functions like start_dev, run_tests, etc.)...

# ---
# Executes the offline data pipeline to build the global Mathlib graph.
# This script must be run from within the devcontainer.
# It assumes the Python environment is activated and dependencies are installed.
# ---
run_pipeline_mathlib() {
   echo "--- Starting Mathlib Global Graph Construction Pipeline ---"
   echo "This process may take a significant amount of time."

   # Execute the script installed via pyproject.toml
   # The script will handle its own logging to console and file.
   build-mathlib-graph

   local exit_code=$?
   if [ $exit_code -eq 0 ]; then
       echo "--- ✅ Pipeline execution finished successfully. ---"
       echo "--- Check detailed logs in backend/logs/pipeline.log ---"
   else
       echo "--- ❌ Pipeline execution failed with exit code $exit_code. ---"
       echo "--- Check detailed logs in backend/logs/pipeline.log for errors. ---"
   fi
}

# --- Main command router ---
case "$1" in
   start)
       start_dev
       ;;
   test)
       run_tests
       ;;
   run-pipeline:mathlib)
       run_pipeline_mathlib
       ;;
   *)
       echo "Usage: $0 {start|test|run-pipeline:mathlib}"
       exit 1
       ;;
esac

This integration plan provides a clear path to replace the legacy data systems with the new Neo4j-backed knowledge graph, ensuring minimal disruption and providing a robust, maintainable, and powerful foundation for the future of the Altera Labs project.
Works cited
                              1. frenzymath/jixia: A static analysis tool for Lean 4. - GitHub, accessed August 30, 2025, https://github.com/frenzymath/jixia
                              2. 4. Declarations — The Lean Reference Manual 3.3.0 documentation, accessed August 30, 2025, https://leanprover.github.io/reference/declarations.html
                              3. Herald: A Natural Language Annotated Lean 4 Dataset - arXiv, accessed August 30, 2025, https://arxiv.org/html/2410.10878v1
                              4. Getting Started — LeanDojo 4.20.0 documentation, accessed August 30, 2025, https://leandojo.readthedocs.io/en/latest/getting-started.html
                              5. digama0/ast_export: AST export from Lean 4 - GitHub, accessed August 30, 2025, https://github.com/digama0/ast_export
                              6. ast - Zulip Chat Archive - Lean community, accessed August 30, 2025, https://leanprover-community.github.io/archive/stream/113488-general/topic/ast.html
                              7. leanprover/lean4export: Plain-text declaration export for ... - GitHub, accessed August 30, 2025, https://github.com/leanprover/lean4export
                              8. Stream: lean4 - Zulip Chat Archive, accessed August 30, 2025, https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Export.20format.html
                              9. Text embeddings API | Generative AI on Vertex AI - Google Cloud, accessed August 30, 2025, https://cloud.google.com/vertex-ai/generative-ai/docs/model-reference/text-embeddings-api
                              10. Get text embeddings | Generative AI on Vertex AI - Google Cloud, accessed August 30, 2025, https://cloud.google.com/vertex-ai/generative-ai/docs/embeddings/get-text-embeddings
                              11. Performance recommendations - Neo4j Python Driver Manual, accessed August 30, 2025, https://neo4j.com/docs/python-manual/current/performance/
                              12. Neo4j Vector Index - Python LangChain, accessed August 30, 2025, https://python.langchain.com/docs/integrations/vectorstores/neo4jvector/
                              13. Seeking Advice on Optimizing ETL Pipeline with SQLAlchemy : r/dataengineering - Reddit, accessed August 30, 2025, https://www.reddit.com/r/dataengineering/comments/1j8r9v7/seeking_advice_on_optimizing_etl_pipeline_with/
                              14. Loading Data into Neo4j Aura - Support, accessed August 30, 2025, https://support.neo4j.com/s/article/1500011497162-Loading-Data-into-Neo4j-Aura
                              15. LOAD CSV - Cypher Manual - Neo4j, accessed August 30, 2025, https://neo4j.com/docs/cypher-manual/current/clauses/load-csv/
                              16. Embeddings for Text – Vertex AI - Google Cloud Console, accessed August 30, 2025, https://console.cloud.google.com/vertex-ai/publishers/google/model-garden/textembedding-gecko?hl=zh-cn&invt=Abh9mw&jsmode
                              17. Lean.Parser.Command, accessed August 30, 2025, https://leanprover-community.github.io/mathlib4_docs/Lean/Parser/Command.html
                              18. Vector indexes - Cypher Manual - Neo4j, accessed August 30, 2025, https://neo4j.com/docs/cypher-manual/current/indexes/semantic-indexes/vector-indexes/
                              19. leanprover-community/mathlib4: The math library of Lean 4 - GitHub, accessed August 30, 2025, https://github.com/leanprover-community/mathlib4
                              20. Using mathlib4 as a dependency - GitHub, accessed August 30, 2025, https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency
                              21. lean4 - Mathlib is downloaded every time a new project is created, accessed August 30, 2025, https://proofassistants.stackexchange.com/questions/4647/mathlib-is-downloaded-every-time-a-new-project-is-created
                              22. Embeddings | Gemini API | Google AI for Developers, accessed August 30, 2025, https://ai.google.dev/gemini-api/docs/embeddings
                              23. Import data - Neo4j Performance Guide, accessed August 30, 2025, https://neo4j-guide.com/neo4j-slow-import-data-performance/
                              24. Loading CSV files - Neo4j Aura, accessed August 30, 2025, https://neo4j.com/docs/aura/classic/aurads/importing-data/load-csv/
                              25. Import - Operations Manual - Neo4j, accessed August 30, 2025, https://neo4j.com/docs/operations-manual/current/import/
                              26. Importing CSV Files in Neo4j - Medium, accessed August 30, 2025, https://medium.com/data-science/importing-csv-files-in-neo4j-f3553f1a76cf