# **Altera Labs - The AI Cognitive Partner**

Altera Labs is a student-led venture from Johns Hopkins University dedicated to building a pedagogically superior AI tutor for STEM education. Our mission is to create an **AI Cognitive Partner** that enhances a student's critical thinking skills, rather than just providing answers. 
This project has evolved beyond its initial "Proof State Auditor" MVP into a more comprehensive learning platform. It now features a sophisticated, multi-modal architecture designed to support students through their entire learning lifecycle, from understanding concepts to completing assignments and preparing for exams.

## **✨ Core Features**

The application is designed around two primary workflows: a collaborative **Homework Mode** and a high-stakes **Exam Mode**.

* **Syllabus-Driven Knowledge Graph**: Users begin by uploading a class syllabus (.pdf, .txt). The AI analyzes it and generates a dynamic, interactive **Knowledge Graph** of the course's key concepts and their dependencies.
* **Contextual Inquiry ("Highlight-to-Ask")**: While interacting with the AI, students can highlight any term or phrase to get a clear, university-level explanation tailored to the current context.
* **The Socratic Verifier**: The cornerstone of the application, now enhanced with a more robust backend.
    * **Metacognitive Scaffolding**: The AI guides students through a **Plan-Monitor-Reflect** cycle, prompting them to articulate their strategy and reflect on their learning.
    * **Natural Language to Formal Verification**: Students propose proof steps in plain English or LaTeX. The system translates this into formal Lean 4 tactics and verifies them for logical correctness using a real Lean compiler.
    * **Pedagogical Feedback**: If a step is incorrect, the AI uses the compiler's error to generate a targeted, Socratic hint, guiding the student without giving away the answer.
* **Advanced Student Modeling**: The system uses Bayesian Knowledge Tracing (BKT) to build a persistent, personalized model of each student's mastery and uncertainty for every concept in the knowledge graph.

## **🛠️ Technology Stack**

| Component       | Technologies                                                                   |
| :-------------- | :----------------------------------------------------------------------------- |
| **Backend** | Python 3.11, Flask, **Google Cloud Vertex AI (Gemini Models)**, Lean 4 (via lake) |
| **Frontend** | React, Vite, **TypeScript**, Tailwind CSS, **D3.js** |
| **Development** | VS Code Dev Containers, Docker                                                 |

## **🏛️ Project Architecture**

The application uses a modular, pedagogically-driven client-server model.

1.  **Web Layer (app.py)**: The Flask application serves as the main API gateway. It manages user sessions via secure cookies and orchestrates the backend modules based on the user's current mode (Homework/Exam).
2.  **Socratic Auditor Engine (socratic\_auditor.py)**: This is the core reasoning engine. It uses models hosted on **Vertex AI** to perform the initial translation of informal user input into Lean Syntax objects. It then uses the Lean 4 compiler's metaprogramming features to rigorously verify the logic and generate precise error messages.
3.  **Pedagogical Strategy Engine (metacognition.py)**: This module is the "brain" of the conversational flow. It manages the user's state within the **Plan-Monitor-Reflect** cycle and uses the student's dynamic knowledge model to tailor its feedback, hints, and overall strategy.
4.  **RAG Manager (rag\_manager.py)**: This module handles the persistence of user-uploaded documents, such as syllabi and homework assignments, forming the foundation of our Retrieval-Augmented Generation pipeline.

## **🚀 Getting Started**

This project is configured to use VS Code Dev Containers, which is the **highly recommended** way to get started.

### **Prerequisites**

1.  **Docker Desktop**: [Install from the official website](https://www.docker.com/products/docker-desktop/).
2.  **Visual Studio Code**: [Install from the official website](https://code.visualstudio.com/).
3.  **VS Code Dev Containers extension**: [Install from the VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers).
4.  **Google Cloud SDK**: [Install and configure the gcloud CLI](https://cloud.google.com/sdk/docs/install) to handle Vertex AI authentication.

### **Steps**

1.  **Clone the Repository & Open in VS Code.**

2.  **Authenticate with Google Cloud**:
    Before building the container, authenticate your local environment so the container can inherit the credentials.
    ```bash
    gcloud auth application-default login
    ```

3.  **Configure Environment Variables**:
    The project requires a `FLASK_SECRET_KEY` to securely sign user session cookies, which is a critical security feature. This key should not be committed to git.

    * **For Dev Container Users (Recommended)**: The `VERTEX_AI_PROJECT_ID` and `VERTEX_AI_LOCATION` are set automatically by the `.devcontainer/devcontainer.json` file. You only need to generate the Flask secret key. Run the following command from the project's root directory to create the `backend/.env` file with a secure, random key:
        ```bash
        python -c 'import secrets; print(f"FLASK_SECRET_KEY=\"{secrets.token_hex(24)}\"")' > backend/.env
        ```

    * **For Local/Manual Setup**: If you are not using the Dev Container, you must create a `.env` file in the `backend` directory and add all required variables:
        ```env
        # backend/.env
        VERTEX_AI_PROJECT_ID="your-gcp-project-id"
        VERTEX_AI_LOCATION="your-gcp-region" # e.g., us-central1
        FLASK_SECRET_KEY="use-the-python-command-above-to-generate-a-real-key"
        ```
    *Note: The `LAKE_EXECUTABLE_PATH` is set automatically within the Dev Container.*

4.  **Reopen in Container**:
    Open the project folder in VS Code. A pop-up will appear in the bottom-right corner. Click "Reopen in Container". This will build the Docker image and configure the environment, which may take several minutes on the first run.

5.  **Run the Application**:
    Once the container is running, use two separate terminals inside VS Code (`Terminal > New Terminal`).

    * **Terminal 1: Start the Backend Server**
        ```bash
        # This command is run from the root of the workspace
        python -m backend.app
        ```

    * **Terminal 2: Start the Frontend Server**
        ```bash
        # This command is also run from the root of the workspace
        cd frontend
        npm install
        npm run dev
        ```
    You can now open `http://localhost:5173` in your browser.

## **🗺️ Roadmap & Future Vision**

Our development is guided by a phased plan to progressively build out the AI Cognitive Partner's capabilities.

* ✅ **Phase 1: Foundational Backend & UI Refactoring**
    * Migrated to Google Cloud Vertex AI.
    * Implemented robust session management.
    * Established "Homework" and "Exam" modes.
    * Built the RAG file-handling infrastructure.
* ➡️ **Phase 2: Knowledge Graph & User-Facing Analytics (In Progress)**
    * ✅ Implemented interactive, syllabus-driven Knowledge Graph generation.
    * ✅ Implemented "Highlight-to-Ask" for contextual concept explanations.
    * *Up Next:* Fix UI issues and create distinct pages
    * *Up Next:* A post-exam results screen with a personalized review plan.
    * *Up Next:* Full integration of the SessionView for interactive proof-auditing.
* *Future:* **Phase 3: Advanced AI & Personalization**
    * AI-driven "pre-work" where the tutor solves homework to provide better guidance.
    * Affective computing to detect and respond to student frustration.

