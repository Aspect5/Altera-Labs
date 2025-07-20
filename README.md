# Altera Labs - The AI Cognitive Partner

Altera Labs is a student-led venture from Johns Hopkins University dedicated to building a pedagogically superior AI tutor for STEM education. Our mission is to create an **AI Cognitive Partner** that enhances a student's critical thinking skills, rather than just providing answers.

This project is the backend and frontend for our "Proof State Auditor" MVP, a specialized AI tutor designed to guide students through formal mathematical proofs.

---

## ✨ Core Features

* **Syllabus Concept Extraction**: Users can upload a class syllabus (`.pdf` or `.txt`), and the AI will analyze it to extract a list of key concepts for the course.
* **Concept Explanation**: Users can click on an extracted concept to get a concise, university-level explanation.
* **The Socratic Verifier (Proof Auditor)**: The cornerstone of the application.
    * **Natural Language Interaction**: Students propose their next step in a proof using plain English or describe their conceptual thinking.
    * **Intent-Aware Routing**: The system intelligently determines if the user is attempting a formal `PROOF_STEP`, describing a `CONCEPTUAL_STEP`, asking a `QUESTION`, or making a general comment.
    * **Formal Verification**: User steps are translated into formal Lean 4 tactics and verified for logical correctness using a real Lean compiler.
    * **Socratic Feedback**: If a step is incorrect, the AI uses the compiler's error to generate a targeted, pedagogical hint, guiding the student without giving away the answer.

---

## 🛠️ Technology Stack

| Component          | Technologies                                                     |
| ------------------ | ---------------------------------------------------------------- |
| **Backend** | Python 3.11, Flask, Google Gemini API, Lean 4 (via `lake`)       |
| **Frontend** | React, Vite, Tailwind CSS, CodeMirror                            |
| **Development** | VS Code Dev Containers, Docker, Conda, Node.js                   |

---

## 🚀 Getting Started

This project is configured to use VS Code Dev Containers, which is the **highly recommended** way to get started. It automatically sets up a consistent and fully-configured development environment with all necessary tools and dependencies.

### Option 1: Recommended Setup (VS Code Dev Containers)

This method automates the installation of Python, Node.js, the Lean 4 toolchain, and all project dependencies.

#### Prerequisites

1.  **Docker Desktop**: Install it from the [official Docker website](https://www.docker.com/products/docker-desktop/).
2.  **Visual Studio Code**: Install it from the [official VS Code website](https://code.visualstudio.com/).
3.  **VS Code Dev Containers extension**: Install this from the [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers).

#### Steps

1.  **Clone the Repository:**
    ```bash
    git clone <your-repository-url>
    cd Altera-Labs
    ```

2.  **Create the Backend `.env` file:**
    Navigate to the `backend` directory and create a file named `.env`. This file is required to store your API key.
    ```bash
    cd backend
    touch .env
    ```
    Add the following content to the `backend/.env` file:
    ```dotenv
    # .env file for Altera Labs Backend

    # Your Google AI Studio API Key
    GEMINI_API_KEY="YOUR_GEMINI_API_KEY_HERE"
    ```
    *Note: The `LAKE_EXECUTABLE_PATH` is set automatically within the Dev Container.*

3.  **Open in Dev Container:**
    Open the `Altera-Labs` folder in VS Code. A pop-up will appear in the bottom-right corner. Click **"Reopen in Container"**.

    VS Code will now build the Docker image and configure the environment. This may take several minutes on the first run as it downloads all the necessary components. The `post-create.sh` script will automatically install all Python and Node.js dependencies.

4.  **Run the Application:**
    Once the container is built and your VS Code has reloaded, you can start the application. You will need **two separate terminals** inside VS Code. You can open a new terminal with `Terminal > New Terminal`.

    **Terminal 1: Start the Backend Server**
    ```bash
    # This command is run from the root of the workspace
    python backend/app.py
    ```
    The backend will be available inside the container on port 5000.

    **Terminal 2: Start the Frontend Server**
    ```bash
    # This command is also run from the root of the workspace
    cd frontend
    npm run dev
    ```
    The frontend will be available on port 5173. VS Code should automatically forward this port, allowing you to open `http://localhost:5173` in your local browser to use the application.

### Option 2: Alternative (Manual Setup)

If you cannot use Docker or Dev Containers, you can set up the project manually.

#### Prerequisites

* **Conda**: For Python environment management.
* **Node.js**: v18.x or later.
* **Lean 4 Toolchain**: Install via `elan` from the [official Lean 4 installation instructions](https://lean-lang.org/install/).

#### Steps

1.  **Clone & Configure Backend:**
    * `git clone <your-repository-url>`
    * `cd Altera-Labs/backend`
    * Create the `.env` file as described in Step 2 of the containerized setup. **Crucially**, you must now also manually find and set the `LAKE_EXECUTABLE_PATH`.
        ```dotenv
        # Find this by running 'which lake' (macOS/Linux) or 'where lake' (Windows)
        LAKE_EXECUTABLE_PATH="/path/to/your/.elan/bin/lake"
        ```
    * Install Python dependencies: `pip install -r requirements.txt`

2.  **Configure Frontend:**
    * `cd ../frontend`
    * Install Node.js dependencies: `npm install`

3.  **Run the Application:**
    Follow Step 4 from the containerized setup, running the backend and frontend servers in two separate local terminals.

---

## 🏛️ Project Architecture

The application follows a client-server model with a unique backend loop for proof verification.

1.  **User Onboarding**: A user can upload a syllabus to the `/api/addClass` endpoint, which uses an LLM to extract key concepts for a "Class".
2.  **Launching the Auditor**: The user launches the **Proof Auditor**, which calls `/api/startSession` to initialize a new proof attempt.
3.  **The Interactive Loop**: Inside the **Session View**:
    * The user sends a message to the `/api/message` endpoint.
    * The backend's **Intent Router** classifies the message (`PROOF_STEP`, `CONCEPTUAL_STEP`, `QUESTION`, etc.).
    * If it's a proof attempt, the backend uses an LLM to generate a Lean 4 tactic.
    * This tactic is injected into a temporary proof file and compiled by the **Lean Verifier** (`lake build`).
    * **If it verifies:** The proof state is updated, and a confirmation is sent.
    * **If it fails:** The compiler error is used by another LLM call to generate a **Socratic hint**.
    * The AI's final response and the updated proof state are sent back to the frontend.

---

## 🗺️ Roadmap & Future Vision

Our goal is to evolve beyond the MVP by building out our "Four Vectors" of pedagogical differentiation.

* **Metacognitive Scaffolding**: Move beyond step-by-step verification to explicitly teach problem-solving strategies.
* **Affective Computing**: Integrate emotion detection to respond to student frustration with increased support.
* **Dynamic Knowledge Modeling**: Build a persistent, personalized Knowledge Graph for each student.
* **Immersive Pedagogy**: Replace static text responses with interactive visualizations and "Explorable Explanations."

