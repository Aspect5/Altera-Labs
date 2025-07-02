# Altera Labs - The AI Cognitive Partner

Altera Labs is a student-led venture from Johns Hopkins University dedicated to building a pedagogically superior AI tutor for STEM education. Our mission is to create an **AI Cognitive Partner** that enhances a student's critical thinking skills, rather than just providing answers.

This project is the backend and frontend for our "Proof State Auditor" MVP, a specialized AI tutor designed to guide students through formal mathematical proofs.

---

## ✨ Core Features (Current)

*   **Syllabus Concept Extraction**: Users can upload a class syllabus (`.pdf` or `.txt`), and the AI will analyze it to extract a list of key concepts for the course.
*   **Concept Explanation**: Users can click on an extracted concept to get a concise, university-level explanation.
*   **The Socratic Verifier (Proof Auditor)**: The cornerstone of the application.
    *   **Natural Language Interaction**: Students propose their next step in a proof using plain English.
    *   **Intent-Aware Routing**: The system intelligently determines if the user is attempting a proof step, asking a question, or making a comment.
    *   **Formal Verification**: User steps are translated into formal Lean 4 tactics and verified for logical correctness using a real Lean compiler.
    *   **Socratic Feedback**: If a step is incorrect, the AI uses the compiler's error to generate a targeted, pedagogical hint, guiding the student without giving away the answer.

---

## 🛠️ Technology Stack

| Component      | Technologies                                               |
| -------------- | ---------------------------------------------------------- |
| **Backend**    | Python 3.11, Flask, Conda, Google Gemini API, Lean 4 (via `lake`) |
| **Frontend**   | React, Vite, Tailwind CSS, CodeMirror                      |
| **Dev Tools**  | VS Code (Multi-Root Workspace recommended)                 |

---

## 🚀 Getting Started

Follow these instructions to get the development environment set up and running on your local machine.

### 1. Prerequisites

Ensure you have the following software installed on your system:

*   **Conda**: [Anaconda](https://www.anaconda.com/products/distribution) or [Miniconda](https://docs.conda.io/en/latest/miniconda.html) for Python environment management.
*   **Node.js**: Version 18.x or later. We recommend using [nvm](https://github.com/nvm-sh/nvm) to manage Node versions.
*   **Lean 4 Toolchain**: Install via `elan` by following the [official Lean 4 installation instructions](https://lean-lang.org/install/).

### 2. Initial Setup

#### Step A: Clone the Repository

```bash
git clone <your-repository-url>
cd Altera-Labs
```

#### Step B: Configure the Backend

1.  **Navigate to the backend directory:**
    ```bash
    cd altera-backend
    ```

2.  **Create the `.env` file:** Create a new file named `.env` in this directory and add the following content. This file stores your secret keys and local paths.

    ```dotenv
    # .env file for Altera Labs Backend

    # Your Google AI Studio API Key
    GEMINI_API_KEY="YOUR_GEMINI_API_KEY_HERE"

    # Full, absolute path to your 'lake' executable.
    # Find this by running 'which lake' (macOS/Linux) or 'where lake' (Windows) in your terminal.
    LAKE_EXECUTABLE_PATH="/path/to/your/.elan/bin/lake"

    # Optional: Only needed if you are on a network with an SSL proxy (e.g., university or corporate VPN)
    # REQUESTS_CA_BUNDLE="/path/to/your/certificate.pem"
    ```

3.  **Create the Lean Verifier Project:** Our backend needs a dedicated Lean project to use as a sandbox. Run this command from the `altera-backend` directory:
    ```bash
    lake new lean_verifier math
    ```
    This creates a `lean_verifier` folder, which our Python script is configured to use.

4.  **Create the Conda Environment:** This command reads the `environment.yml` file and installs all required Python packages into an isolated environment named `altera-labs`.
    ```bash
    conda env create -f environment.yml
    ```

#### Step C: Configure the Frontend

1.  **Navigate to the frontend directory:**
    ```bash
    # From the altera-backend directory
    cd ../altera-frontend
    ```

2.  **Install Node.js dependencies:**
    ```bash
    npm install
    ```

### 3. Running the Application

You will need **two separate terminals** running simultaneously.

**Terminal 1: Start the Backend Server**

```bash
# Navigate to the backend folder
cd altera-backend

# Activate the Conda environment
conda activate altera-labs

# Run the Flask app
python app.py
```
You should see output indicating the server is running on `http://127.0.0.1:5000`.

**Terminal 2: Start the Frontend Server**

```bash
# Navigate to the frontend folder
cd altera-frontend

# Run the Vite development server
npm run dev
```
You should see output indicating the frontend is available at a local URL, typically `http://localhost:5173`.

**Usage:**
Open the frontend URL (e.g., `http://localhost:5173`) in your web browser to use the application.

---

## 🏛️ Project Architecture

The application follows a standard client-server model but with a unique backend loop for proof verification.

1.  **User Onboarding**: The user starts at the **Dashboard**, where they can upload a syllabus to create a "Class". The backend's `/addClass` endpoint uses an LLM to parse the syllabus and extract key concepts.
2.  **Launching the Auditor**: From the Dashboard, the user launches the **Proof Auditor**. This calls `/startSession` to initialize a new proof attempt.
3.  **The Interactive Loop**: Inside the **Session View**:
    *   The user sends a message.
    *   The backend's `/sendMessage` endpoint first uses an **Intent Router** to classify the message (`PROOF_STEP`, `QUESTION`, `META_COMMENT`).
    *   If it's a `PROOF_STEP`, the backend uses an LLM to generate a Lean 4 tactic.
    *   This tactic is injected into the proof file and compiled by the **Lean Verifier** (`lake build`).
    *   **If it verifies:** The proof state is updated, and a confirmation is sent.
    *   **If it fails:** The compiler error is used by another LLM call to generate a **Socratic hint**.
    *   The AI's final response and the updated proof state are sent back to the frontend.

---

## 🗺️ Roadmap & Future Vision

Our goal is to evolve beyond the MVP by building out our "Four Vectors" of pedagogical differentiation.

*   **Metacognitive Scaffolding**: Move beyond step-by-step verification to explicitly teach problem-solving strategies like **Plan-Monitor-Reflect**. The AI will ask students to state their plan *before* writing code.
*   **Affective Computing**: Integrate emotion detection (based on text pace, phrasing, and explicit feedback) to respond to student frustration with increased support or a change in strategy.
*   **Dynamic Knowledge Modeling**: Use the concepts extracted from the syllabus to build a persistent, personalized **Knowledge Graph** for each student. Track mastery of concepts using Bayesian Knowledge Tracing (BKT) based on their success and failure in proofs.
*   **Immersive Pedagogy**: Replace static text responses with interactive visualizations and "Explorable Explanations," allowing students to manipulate variables and see the mathematical consequences in real-time.