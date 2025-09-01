1. Name of your venture

[WRITE HERE] AI Cognitive Partner
2. Please share your website or any social media links below:

[WRITE HERE] N/A
If you do not a website or social media presence, please put "N/A"

3. Applicant name (last name, first name)

[WRITE HERE] Kroumov, Alex; Seelman, Peter; Lonske, Akira
4. Email Address

[WRITE HERE] ikroumo1@jh.edu

5. JHU School

Whiting School of Engineering; Krieger School of Arts and Sciences

6. Please list the specific department associated with your degree.

Biomedical Engineering

7. Academic Status

Undergraduate
8. Please type your anticipated graduation date below

May 2027

9. Which accelerator are you applying to?

Fuel

10. Are there other team members? If so, check, and fill out information:

You must include info for EACH team member: 



If JHU, fill out: Last name, first name, email, what academic program and major or department is this individual affiliated with and anticipated graduation. Example: "Davidson, Paul, <paul.davidson@jhu.edu>, Economics, May 2026"

Seelman, Peter, pseelma1@jh.edu, Physics, May 2027
Lonske, Akira, alonske1@jh.edu, Computer Science, May 2027


If NOT affiliated with JHU, type if there is an affiliation with another university or employer and include their email address.  Only team members with an equity stake or co-founder status need to be listed. 

11. Who will be the lead(s) for your team?

[WRITE HERE] Peter Seelman
Accelerators require a consistent person to attend sessions who will also serve as the main point of contact. 

12. Please describe your venture idea (1 paragraph)

[WRITE HERE] Conversational tutoring bot interface integrated with a theorem prover and a custom knowledge tracing and visualization architecture

Altera Labs is developing an AI Cognitive Partner to provide trustworthy, verifiable reasoning for complex problem-solving. Traditional education struggles with a 'one-size-fits-all' model, and current AI tools are unreliable, prioritizing fluency over accuracy. Our system solves this by using a multi-agent architecture that can reason through problems and have its solutions formally verified. We are pioneering this approach in higher-level mathematics, using a Lean 4 proof assistant to guarantee correctness. This domain serves as the perfect training ground for our core engine. This engine, combined with our novel knowledge graphing and emotional state monitoring, creates a hyper-personalized and reliable learning experience that we plan to expand to other STEM fields, corporate training, and beyond.



\




13. Describe the problem your idea/venture addresses in under three sentences:

[WRITE HERE] 
The venture addresses three core issues in the current educational and AI landscape:
AI Unreliability: Current large language models (LLMs) are fundamentally unreliable for complex problem-solving, as their probabilistic nature prioritizes fluent-sounding answers over verifiable accuracy.
Legacy System Rigidity: Existing intelligent tutoring systems are rigid and emotionally unaware, using inflexible knowledge tracking methods while lacking the affective computing needed to monitor a student's emotional state.
The Market Gap: Consequently, no hybrid platform exists that combines a verifiable reasoning engine for trustworthy guidance with dynamic, emotionally-aware knowledge tracking to create a truly personalized and effective learning experience.

14. What progress have you've already achieved on this project? (Response should be no more than a paragraph) 


Our architectural design is deeply informed by a Bible’s worth of research papers and reports that we have compiled, guiding our development from concept to a functional MVP. This MVP currently features a frontend and backend that allows students to upload a syllabus and generate a connected concept graph of the course material. The core of our progress is a preliminary mathematical verification system that uses a Lean 4 proof assistant to check the correctness of AI-generated outputs, a feature designed to foster critical thinking by guiding students without providing direct answers. While this system is functional, it is still in its early stages, and we are actively working to build out its capabilities to handle more complex mathematical reasoning. We've also incorporated key learnings from a previous project, HumorHealer, by migrating its emotional state tracking technology into our current platform. The experience from developing that initial concept, including our participation in the Spark Accelerator and the NSF I-Corps program, has provided valuable insights into user needs and product design, which we are now applying to Altera Labs.


[TALK MORE ABOUT THE BAYSEIAN KNOWLEDGE TRACKING!!!!]
Bayesian knowledge tracking itself is a method of estimating a mean level of knowledge of a concept using four numeric parameters. The system in place modifies this principal by employing bayesian inference on a matrix of random variables that correlates concepts through natural language, and assigns a mean and uncertainty to the probable level of mastery of a concept.



Our system modifies the standard four-parameter Bayesian Knowledge Tracing model by applying Bayesian inference to a vector of random variables that correlate related concepts. This approach not only estimates a student's mastery level but also quantifies the uncertainty of that knowledge for each concept in the concept vector, providing a more nuanced and accurate picture of their learning progress across interconnected topics.


[WRITE HERE]
This can include progress towards an MVP, other accelerators or competitions, customer discovery, etc. 
spark and icorp
summer work on intelligent tutoring system
MVP is currently for tutoring system but we are discovering it can be used for anything, and the agentic and verifiability can be used for economic strategy
need mentorship to figure out this 

15. Describe your venture’s approach to addressing this problem/opportunity. How is the approach unique? (5 sentences max)

Our approach is uniquely centered on a verifiable reasoning engine, designed for rapid expansion across complex subjects. A student first uploads their syllabus, which our system transforms into a personalized concept graph of the course material. When the student submits a problem, our AI agents construct a logical solution that, for our proof-of-concept in higher-level mathematics, is rigorously checked using a Lean 4 proof assistant to guarantee correctness. This verified solution then powers a one-of-a-kind tutoring experience, guided by the student's unique knowledge graph and emotional state. This foundational model of combining a verifiable core with deep personalization is our blueprint for scaling to other STEM fields, corporate training, and beyond.

16. What are some current difficulties your venture is facing?

Our core innovation lies in creating a system that can produce mathematically verifiable proofs. The main hurdle here is autoformalization, an open research challenge centered on a fundamental question: can machines think logically? This is an active frontier of AI research, which Peter had the opportunity to see firsthand at an APL colloquium led by Johns Hopkins' own Professor Emily Riehl. The central difficulty is bridging the gap between the probabilistic nature of current LLMs and the deterministic rigor required for formal mathematical proofs. We are, in essence, tackling a foundational research problem as a core part of our venture.

A second, more concrete challenge is the sheer engineering effort required to build our GraphRAG knowledge base for Lean 4's Mathlib, a massive digital library of formal mathematics. Our plan is to transform this library into a structured knowledge graph, for which we've identified Neo4j as the optimal database technology. For an early-stage startup, the primary difficulty is the significant upfront financial and logistical lift required to get this system set up. It involves building a complex data pipeline to ingest and process the entirety of Mathlib, which requires substantial computational resources. A key question we're currently grappling with is how to best implement this architecture—specifically, how much of the pipeline to build ourselves versus leveraging the powerful tools within the Neo4j ecosystem. We believe the accelerator's mentorship on technical strategy and resource allocation would be crucial in helping us navigate this foundational setup cost-effectively.

Looking ahead, our third major challenge is adapting our core principle of "verifiability" to disciplines like physics and computer science to expand our, which lack a universal formal verifier like Lean 4 proof assistants. To solve this, our strategy is to evolve from formal verification to a model of computational and consensual validation. We are designing a multi-agent system where several independent AI agents solve a problem using different approaches. A solution's trustworthiness is then established through two mechanisms:
Consensus: Do the independent agents arrive at the same answer and reasoning?
Computational Check: Can the solution be validated through execution? For a physics problem, this might mean running a simulation based on the AI's derived equations. For a computer science problem, it would involve executing the generated code against a set of unit tests. This multi-pronged approach is key to our expansion, and a primary goal within the Fuel accelerator would be to refine this strategy and build a robust roadmap for scaling our trustworthy AI partner across the STEM landscape.

17. What are you hoping to get out of the accelerator opportunity? Please list skills you’d like to hone or progress you’d like to make during the semester. 


Mentors for


help with the architecture
reactive instead of proactive (?) is that even a weakness
We would like to develop our product by eos

Features We’d Like to Develop:

We want to dive deeper into personalized learning, adding the ability to generate quizzes based off of lecture content. 



Our primary goal for the Fuel accelerator is to transition Altera Labs from a powerful proof-of-concept into a scalable platform with a clear path to market. We are seeking mentorship and structure to achieve this in three key areas:
Technical & Architectural Strategy: We have designed a complex system but face significant engineering hurdles, particularly in building out our GraphRAG knowledge base for Mathlib using Neo4j. We are seeking expert guidance on the most efficient way to build this foundational data pipeline, helping us navigate the critical "build vs. buy" decisions for an early-stage venture.
Product Roadmap Development: Our biggest strategic challenge is adapting our core principle of "verifiability" from formal mathematics to other domains like physics and computer science. We need mentorship to help refine our proposed "computational and consensual validation" model and build a concrete, prioritized roadmap for expanding our feature set beyond our initial market.
Go-to-Market Refinement: Building on our experience in the NSF I-Corps program, we aim to hone our business strategy. We would like to work with mentors to validate our institutional licensing model and develop a concrete plan for customer acquisition, starting with STEM departments at Johns Hopkins and other research universities.
By the end of the semester, we aim to have made the following concrete progress:
Solidify Core Architecture: Fully implement the initial GraphRAG knowledge base for Mathlib, moving from a conceptual design to a functional backend capable of supporting our verification engine.
Prototype Expansion Model: Develop and test an early prototype of our multi-agent "consensual validation" system for a non-mathematical use case (e.g., a simple physics problem), proving the core thesis of our expansion strategy.
Enhance Personalization Features: Implement our planned feature to generate personalized quizzes based on lecture content, deepening the adaptive learning experience for users.

18. How much funding, if any, has your venture secured, so far? From what sources?

[WRITE HERE]
We have secured 500$ previously in our venture from last year’s Spark accelerator, and have iterated greatly on our idea since after using these funds to acquire credits and a web domain. 

19. How do you anticipate generating revenue? Please explain your business model in the near term, to the best of your ability.

[WRITE HERE] 

Altera Labs will first focus on gaining endorsement through educational institutions with a strong focus on AI and mathematics such as Johns Hopkins. These institutions are ideal candidates for partnership due to their high volume of academic publications and high STEM student population, an indication of a strong research community. This strategy enables us to gain endorsements from leading researchers and students who will advocate for the adoption of our tool. Our business model can be divided into two key areas: institutional licensing combined with strategic cost advantage.

Institutional licensing strategy includes licensing the cognitive partner to the educational institution. The subscription model offers predictable revenue stream and scalable cost for the university based on usage, with the core incentive being to increase research output.

Additionally, Altera Labs offers a significant competitive advantage. Unlike generalized models which are costly to train and run, the AI cognitive partner’s multi-agent system is built for mathematical reasoning and verification. This translates to lower operational costs, allowing us to offer a more affordable solution than competitors. We aim to find a price point that acknowledges the current financial struggle educational institutions face while still generating a healthy profit margin. This makes our AI cognitive partner a more sustainable long-term investment in the research and ed-tech space. In the future, we see the potential of a cognitive partner in learning any intellectual skill, which includes company onboarding, training, and tutoring.



20. If your venture is selected, how do you anticipate utilizing any grant money received?


Cloud Compute Total based on conservative testing only (i.e. 1600 hours per month, ) $662.93/month = $6629.30/year
https://cloud.google.com/products/calculator?dl=CjhDaVE0T0RjMk1Ea3pPUzA0WXpVMExUUmtNell0WVdZd01pMDVPVGcxWXpaaE4yTmtNamdRQVE9PRARGiQ5MzhCMEU2MC03OTIwLTQ4NkQtODc2NC1EOTUyQjE0QkM3NTg&hl=en
Vertex AI - $75.74/month
GKE - $194.82/month
Compute - $154.04/month
Cloud GPU - $113.09
SQL database - $25.34
Cloud storage - $99.90
These are assumptions based on conservative usage
Cloud Compute Total based on 100 users making 100 requests per day for 30 days
https://cloud.google.com/products/calculator?hl=en&dl=CjhDaVJoWVRsbE16UTVNQzB4TlRobUxUUmxNMkV0WVdWaE1TMWhZVEExWlRVek0yRTVZbVVRQVE9PRAJGiQwQkEyMjFGRi1CMjFCLTRFREUtODFEQy0wMTJDOTgzRjVBRTk
Web domain cost
$50/year
10% for emergency expenses including spontaneous fees for software, sudden meetings

Total: $7369.89 - which is enough for one entire year
The costs and needs will be adjusted as grant money is awarded. 

21. Incorporation Status 

[WRITE HERE] Unincorporated

22. Does JHU own any of the intellectual property of your venture?

[WRITE HERE] No 

23. Are you working with any faculty/staff members on this venture? If so, list names, departments, and their role in your venture.

[WRITE HERE] No

24. Is there anything we didn’t ask that we should know? Feel free to include how you feel personally connected to your venture, and any other goals you have for the experience.
As students in math-intensive majors at JHU, we are all too familiar with the feeling of staring at a chalkboard of incomprehensible symbols, rushing to take notes, and telling ourselves we'll just figure it out later. That feeling of being overwhelmed is the core reason we started this venture. We decided to build the tool we wish we had: an intelligent tutoring system with a tutor who truly understands advanced concepts and can help solve the complex problems we encounter.
We are our own target demographic. This personal connection means we are deeply in-touch with the needs of students and know precisely where current alternatives, like generalized LLMs, fall short. This venture is our solution to enrich our own learning experiences and those of millions of students worldwide. Our goal is to create an AI assistant that, through its innovative and thoughtful approach, provides a level of specialized, trustworthy support that general-purpose tools cannot match

[WRITE HERE]
Bonus: this can be video link to an "elevator speech" (but no pitch decks, please)

I understand that by submitting this application, I am making a serious commitment to my venture and the Pava Center for the semester. Additional terms will be shared if you are selected for either accelerator opportunity.
