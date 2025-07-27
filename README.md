# **Altera Labs - The AI Cognitive Partner**

Altera Labs is a student-led venture from Johns Hopkins University dedicated to building a pedagogically superior AI tutor for STEM education. Our mission is to create an **AI Cognitive Partner** that enhances a student's critical thinking and metacognitive skills, rather than just providing answers.

This project is architected around a core pedagogical principle: preventing harmful **Cognitive Offloading** while promoting beneficial **Cognitive Partnership**. Our system is designed to guide students through an intentional learning process, especially during moments of academic pressure when the temptation to seek easy answers is highest.

## **✨ Core User Experience**

The application workflow is built to be a guided, pedagogically-sound experience from the very first interaction.

1.  **Class Creation**: The user journey begins not with a simple file upload, but with the creation of a **Class**. The user provides a class name and can upload either a **Syllabus** (highly recommended) or a specific **Homework** file. This immediately frames the session within a structured learning context.

2.  **The Proving Agent (Backend Analysis)**: When a homework file is uploaded, our backend initiates a "Proving Agent." This AI agent attempts to solve the problems in a formal verification environment (Lean 4).
    *   **Success:** If solved, the agent generates a "solution graph" of the concepts required. The AI tutor then knows a valid path to the solution and can guide the student effectively.
    *   **Failure:** If the agent fails, it still identifies key concepts it struggled with. This failure is transparently communicated to the student, framing the session as a collaborative exploration: "I tried solving this myself and got stuck, but I learned a few things. Let's look at it together."

3.  **The Cognitive Contract**: Based on the agent's status, the user is presented with a clear path forward. This initial interaction sets the tone for the session, making the user a conscious participant in their own learning strategy.

4.  **Structured Learning Modes**: The application will be structured into distinct modes for studying, practice, assessment, and reflection, ensuring the user is always in an environment tailored to a specific learning goal.

## **🛠️ Technology Stack**

| Component | Technologies |
| :--- | :--- |
| **Backend** | Python 3.10+, Flask, **Google Cloud Vertex AI (Gemini Models)**, Lean 4 (via lake) |
| **Frontend** | React, Vite, **TypeScript**, Tailwind CSS, **D3.js** |
| **Development** | VS Code Dev Containers, Docker |

## **🚀 Getting Started**

This project is configured to use VS Code Dev Containers, which is the **highly recommended** way to get started.

1.  **Prerequisites**: Ensure you have Docker Desktop, VS Code, and the Dev Containers extension installed.
2.  **Authenticate with Google Cloud**: Run `gcloud auth application-default login` in your local terminal before building the container.
3.  **Reopen in Container**: Open the project folder in VS Code and click the "Reopen in Container" prompt. The `post-create.sh` script will handle all dependencies.
4.  **Run the Application**: Once the container is running, use two separate terminals inside VS Code:

    *   **Terminal 1: Start the Backend**
        ```bash
        python -m backend.app
        ```

    *   **Terminal 2: Start the Frontend**
        ```bash
        cd frontend && npm run dev
        ```

    You can now open `http://localhost:5173` in your browser.

