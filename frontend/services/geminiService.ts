
import { GoogleGenAI, Type } from "@google/genai";
import type { GraphNode, Edge, ChatMessage, KnowledgeState, Reassessment, PracticeSuggestion } from '../types';

if (!process.env.API_KEY) {
    throw new Error("API_KEY environment variable not set");
}

const ai = new GoogleGenAI({ apiKey: process.env.API_KEY });

const graphSchema = {
    type: Type.OBJECT,
    properties: {
        nodes: {
            type: Type.ARRAY,
            description: "A list of key technical concepts, which will be the nodes of the graph.",
            items: {
                type: Type.OBJECT,
                properties: {
                    id: {
                        type: Type.STRING,
                        description: "A short, unique, camelCase or snake_case identifier for the concept. E.g., 'chainRule' or 'epsilonDelta'."
                    },
                    label: {
                        type: Type.STRING,
                        description: "A human-readable label for the concept. E.g., 'Chain Rule'."
                    }
                },
                required: ["id", "label"]
            }
        },
        edges: {
            type: Type.ARRAY,
            description: "A list of directed relationships (edges) between the concepts, representing prerequisites.",
            items: {
                type: Type.OBJECT,
                properties: {
                    source: {
                        type: Type.STRING,
                        description: "The ID of the source node (the prerequisite)."
                    },
                    target: {
                        type: Type.STRING,
                        description: "The ID of the target node (the concept that depends on the source)."
                    },
                    weight: {
                        type: Type.NUMBER,
                        description: "A value from 0.0 to 1.0 indicating the strength of the prerequisite link. 1.0 means it's a hard prerequisite."
                    }
                },
                required: ["source", "target", "weight"]
            }
        }
    },
    required: ["nodes", "edges"]
};

export const extractGraphFromSyllabus = async (syllabusText: string): Promise<{ nodes: GraphNode[], edges: Edge[] }> => {
    const prompt = `
        You are an expert in educational theory and computer science. Your task is to analyze the provided course syllabus and construct an educational knowledge graph.

        1.  **Extract Key Concepts:** Identify the main technical topics or concepts from the syllabus. These will be the **nodes** of your graph. Create a unique, simple ID and a clean, human-readable label for each concept.
        2.  **Determine Prerequisites:** Analyze the text to find prerequisite relationships between these concepts. Words like "leads to," "builds upon," "requires," or sequential ordering in the syllabus (e.g., Week 2 topics are prerequisites for Week 3) indicate a relationship. These will be the **edges** of your graph.
        3.  **Assign Weights:** For each prerequisite relationship (edge), assign a numerical **weight** from 0.0 to 1.0.
            *   A weight of ~0.9-1.0 means it's a **hard prerequisite** (e.g., you cannot understand the 'Definition of Derivative' without understanding 'Limits').
            *   A weight of ~0.4-0.7 means it's a **strong suggestion** or helpful concept.
            *   A weight of ~0.1-0.3 means it's a **weakly related** concept.

        Based on the text below, generate the nodes and edges in the specified JSON format.

        **Syllabus Text:**
        ---
        ${syllabusText}
        ---
    `;

    const response = await ai.models.generateContent({
        model: "gemini-2.5-flash",
        contents: prompt,
        config: {
            responseMimeType: "application/json",
            responseSchema: graphSchema,
        },
    });

    const jsonText = response.text.trim();
    const parsedJson = JSON.parse(jsonText);
    
    if (!parsedJson.nodes || !parsedJson.edges) {
        throw new Error("AI response is missing 'nodes' or 'edges' properties.");
    }
    
    return parsedJson as { nodes: GraphNode[], edges: Edge[] };
};

interface MentorResponse {
    responseText: string;
    reassessment?: Reassessment;
    practiceSuggestion?: { nodeId: string; reasoning: string; };
}

const mentorResponseSchema = {
    type: Type.OBJECT,
    properties: {
        responseText: {
            type: Type.STRING,
            description: "The text for the AI mentor to say to the student. Be encouraging and clear."
        },
        reassessment: {
            type: Type.OBJECT,
            description: "Use this IF AND ONLY IF the student's explanation in the latest message gives you strong evidence to update your belief about their knowledge state on a SINGLE concept. Do not use this for practice problem outcomes.",
            properties: {
                nodeId: { type: Type.STRING, description: "The ID of the concept to reassess." },
                reasoning: { type: Type.STRING, description: "A brief justification for why you are reassessing this concept based on the conversation." },
                newMu: { type: Type.NUMBER, description: "The new estimated mastery (a value from 0.0 to 1.0)." },
                newSigma: { type: Type.NUMBER, description: "The new estimated uncertainty (a value from 0.01 to 0.5)." }
            }
        },
        practiceSuggestion: {
            type: Type.OBJECT,
            description: "Use this IF you think the student is ready for a practice problem on a specific topic. Choose a topic that is challenging but not discouraging.",
            properties: {
                nodeId: { type: Type.STRING, description: "The ID of the concept to suggest for practice." },
                reasoning: { type: Type.STRING, description: "A brief justification for why you are suggesting this practice problem." }
            }
        }
    },
    required: ["responseText"]
};


export const getMentorResponse = async (
    history: ChatMessage[],
    knowledgeState: KnowledgeState,
    nodes: GraphNode[]
): Promise<MentorResponse> => {
    const studentKnowledgeString = nodes.map(n => `  - ${n.label} (id: ${n.id}): mu=${knowledgeState[n.id]?.mu.toFixed(2)}, sigma=${knowledgeState[n.id]?.sigma.toFixed(2)}`).join('\n');
    const conversationHistory = history.map(m => `${m.role}: ${m.content}`).join('\n');

    const prompt = `
        You are an expert AI cognitive mentor. Your goal is to help a student learn a set of concepts. You do this through a continuous conversation.

        **Your Capabilities:**
        1.  **Converse:** Engage in a dialogue to explain concepts and answer questions.
        2.  **Assess:** Based on the student's explanations, you can reassess their knowledge level on a specific topic. If their explanation is strong, you can increase their mastery (mu) and decrease uncertainty (sigma). If it's weak, you can do the opposite.
        3.  **Suggest Practice:** When you feel the student is ready, you can suggest a practice problem on a specific topic. You should choose topics they are ready for (e.g., mu between 0.3 and 0.8).

        **Current Student Knowledge State:**
        This is your current belief about the student's knowledge. mu is mastery (0-1), sigma is uncertainty (0-0.5, lower is better).
        ${studentKnowledgeString}

        **Conversation History:**
        ${conversationHistory}

        **Your Task:**
        Based on the **last message** in the conversation history and the student's overall knowledge state, generate your next response. Adhere to the provided JSON schema.
        - If the last message is a user question, answer it.
        - If the user's explanation gives you new insight, use the 'reassessment' field.
        - If you think it's a good time for a challenge, use the 'practiceSuggestion' field.
        - If the last message is a [PRACTICE OUTCOME], respond to their performance. Congratulate success or be encouraging on failure.
        - Keep your 'responseText' conversational and concise.
    `;

    const response = await ai.models.generateContent({
        model: "gemini-2.5-flash",
        contents: prompt,
        config: {
            responseMimeType: "application/json",
            responseSchema: mentorResponseSchema,
        },
    });

    const jsonText = response.text.trim();
    return JSON.parse(jsonText);
};
