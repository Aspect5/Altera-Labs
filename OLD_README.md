# Altera Labs - The AI Cognitive Partner

Altera Labs is a student-led venture from Johns Hopkins University dedicated to building a pedagogically superior AI tutor for STEM education. Our mission is to create an **AI Cognitive Partner** that enhances a student's critical thinking skills, rather than just providing answers.

This project contains the full-stack application for our "Proof State Auditor" MVP, a specialized AI tutor designed to guide students through formal mathematical proofs using the Lean 4 proof assistant.

---

## ✨ Core Features

* **Syllabus Concept Extraction**: Users can upload a class syllabus (`.pdf` or `.txt`), and the AI will analyze it to extract a list of key concepts for the course.
* **Concept Explanation**: Users can click on an extracted concept to get a concise, university-level explanation.
* **The Socratic Verifier (Proof Auditor)**: The cornerstone of the application, featuring a sophisticated interactive loop.
    * **Metacognitive Scaffolding**: The AI guides students through a **Plan-Monitor-Reflect** cycle, prompting them to articulate their strategy before attempting a proof and to reflect on their learning afterward.
    * **Natural Language Interaction**: Students propose their next step in a proof using plain English or describe their conceptual thinking.
    * **Intent-Aware Routing**: The system intelligently determines if the user is attempting a formal `PROOF_STEP`, describing a `CONCEPTUAL_STEP`, asking a `QUESTION`, or making a general comment.
    * **Formal Verification**: User steps are translated into formal Lean 4 tactics and verified for logical correctness using a real Lean compiler.
    * **Socratic Feedback**: If a step is incorrect, the AI uses the compiler's error to generate a targeted, pedagogical hint, guiding the student without giving away the answer.

---

## 🛠️ Technology Stack

| Component | Technologies |
| :--- | :--- |
| **Backend** | Python 3.11, Flask, Google Gemini API, Lean 4 (via `lake`) |
| **Frontend** | React, Vite, Tailwind CSS, CodeMirror |
| **Development** | VS Code Dev Containers, Docker |

---

## 🚀 Getting Started

This project is configured to use VS Code Dev Containers, which is the **highly recommended** way to get started. It automatically builds a consistent and fully-configured development environment with all necessary tools and dependencies.

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
    GEMINI_API_KEY="YOUR_GEMINI_API_KEY_HERE"
    ```
    *Note: The `LAKE_EXECUTABLE_PATH` is set automatically within the Dev Container.*

3.  **Open in Dev Container:**
    Open the `Altera-Labs` folder in VS Code. A pop-up will appear in the bottom-right corner. Click **"Reopen in Container"**.

    VS Code will now build the Docker image and configure the environment. This may take several minutes on the first run. The `post-create.sh` script will automatically install all Python and Node.js dependencies.

4.  **Run the Application:**
    Once the container is built, you can start the application using two separate terminals inside VS Code (`Terminal > New Terminal`).

    **Terminal 1: Start the Backend Server**
    ```bash
    # This command is run from the root of the workspace
    python -m backend.app
    ```

    **Terminal 2: Start the Frontend Server**
    ```bash
    # This command is also run from the root of the workspace
    cd frontend
    npm run dev
    ```
    VS Code will automatically forward the frontend port. You can open `http://localhost:5173` in your local browser to use the application.

### Option 2: Alternative (Manual Setup)

If you cannot use Dev Containers, follow these steps.

#### Prerequisites

* **Python 3.11+**
* **Node.js v18+**
* **Lean 4 Toolchain**: Install via `elan` from the [official Lean 4 installation instructions](https://lean-lang.org/install/).

#### Steps

1.  **Clone & Configure Backend:**
    * `git clone <your-repository-url>`
    * `cd Altera-Labs/backend`
    * Create the `.env` file as described above. You must also manually find and set the `LAKE_EXECUTABLE_PATH`.
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

The application uses a client-server model with a modular, pedagogically-driven backend.

1.  **Web Layer (`app.py`)**: The Flask application serves as the main entry point for API requests. It manages user sessions and delegates all core logic to the other modules.

2.  **Metacognitive Engine (`metacognition.py`)**: This module is the "brain" of the conversational flow. It manages the user's state within the **Plan-Monitor-Reflect** cycle. When a message comes in, it first checks the user's stage:
    * If `PLANNING`, it asks Socratic questions about the user's strategy.
    * If `MONITORING`, it passes the message to the Socratic Auditor for verification.
    * If `REFLECTION`, it prompts the user to reflect on their learning.

3.  **Socratic Auditor (`socratic_auditor.py`)**: This module handles the core verification loop.
    * It uses an LLM (via `prompts.py`) to translate the user's message into a Lean 4 tactic.
    * It runs the Lean compiler in an isolated environment to verify the tactic.
    * If the tactic fails, it uses another LLM call to translate the technical compiler error into a pedagogical Socratic hint.

4.  **Prompt Manager (`prompts.py`)**: This module centralizes all prompts sent to the LLM, making it easy to tune and maintain the AI's behavior and personality.

---

## 🗺️ Roadmap & Future Vision

Our goal is to evolve beyond the MVP by building out our "Four Vectors" of pedagogical differentiation.

* **Affective Computing**: Integrate emotion detection to respond to student frustration with increased support.
* **Dynamic Knowledge Modeling**: Build a persistent, personalized Knowledge Graph for each student.
* **Immersive Pedagogy**: Replace static text responses with interactive visualizations and "Explorable Explanations."

