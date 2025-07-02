Altera Labs' HumorHealer is an AI-powered chatbot designed to provide customizable therapy with a humorous twist, fine-tuned on ethics, clinical guidelines, and comedy materials. It offers 24/7 accessibility and user-guided conversation through SMS messaging or voice-to-voice interaction.

**Current Project Status:**  
The current focus is on improving the first MVP, HumorHealer. Initial contact has been made with Johns Hopkins University (JHU), including the Applied Physics Laboratory, and Dartmouth. Peter Seelman and Alex Kroumov are the co-founders. They have invested $170 on OpenAI, Anthropic credits, and freelance logo design. The system architecture involves using a \`flaskapp1.py\` file with a metaprompt for texting mode, and they are exploring the use of OpenAI's Whisper model for human-like speech and Twilio for text and voice interactions. Data storage methods are being considered, including private, anonymized discussion boards (like Mayo Clinic Connect) that are HIPAA compliant, or public options for non-medical interactions. They are also looking into concepts like LORA (Low-Rank Adaptation) for fine-tuning models and RAG (Retrieval Augmented Generation) for enhancing responses.

**Business Model:**  
Altera Labs plans to use a dynamic subscription business model with tiered pricing. This includes:

* **Direct-to-consumer subscriptions:** Offering various tiers to end-users.  
* **Institutional sales:** Selling HumorHealer directly to universities, high schools, businesses, and the military as part of their mental health services.  
* **Tier upgrades:** Encouraging users to upgrade to higher tiers by providing a model that iteratively improves and remembers past conversations.

The estimated price point for a basic monthly subscription is $5, with tiers potentially including a free trial (Tier 0\) with a message cap, a $10/month tier (Tier 1\) for SMS messaging and limited phone calls, and a $20/month tier (Tier 2\) for unlimited SMS and phone calls. Institutional pricing (Tier 3\) would likely be dynamic and usage-dependent, potentially based on usage volume. Projected revenues for HumorHealer are estimated at $1,236,240.00 in the first year of revenue generation (Year 3 of the financial model), with costs of goods sold at 70% of the price.

**Market and Competition:**  
The target demographic includes high school and college students, and active-duty military personnel. The total addressable market (TAM) for students is estimated at 20 million across 3500 universities, with a potential annual market of $91 million. Studies indicate that 60% of students qualify for a mental health condition, and barriers to seeking help include stigma, time commitment, and a belief that problems will get better without treatment.

HumorHealer differentiates itself by being the only AI therapy chatbot trained to respond with appropriate humor and adapting its humor to individual users, while maintaining core necessities like accessibility, low cost, and custom therapy. Competitor pricing includes OpenAI's GPT-4 at $20/month, Wysa (free limited version, $19.99/month, $74.99/year, or $149.99 lifetime), and Character AI's Psychologist at $10/month. HumorHealer aims to be competitively priced, especially for college students.

**Expert Advice and Traction:**  
Advisors include Paul Berk, who advises on accelerating the venture to schools and the military, and Art Baker, manager for technology acceleration at APL. They have also consulted with Dr. Caroline Popper, an expert in commercializing health tech, and Graham Dodge (VP of TEDCO).

Key advice from I-Corps interviews and other consultations includes:

* **Customer Discovery:** The critical step is to validate the problem, identify who has it, and then determine the best solution. This involves extensive interviewing (aiming for 60-70 for initial insights, up to 100-150 per segment nationally) with potential users, buyers, and decision-makers in institutions. The focus should be on understanding their current workflow, decision-making processes, and pain points (e.g., long waiting lists for therapy, lack of therapist availability, cost). Questions should avoid product bias and instead focus on what makes mental health technology successful from their perspective.  
* **Marketing to Institutions (B2B):** Direct outreach to deans of mental health departments in academic and military institutions is recommended. Initial pilot studies could be offered at no cost to schools, transitioning to paid usage based on data demonstrating effectiveness.  
* **Quantifying Value:** Consider how to quantify the value, potentially using metrics like Quality-Adjusted Life Years (QALYs), or by demonstrating tangible benefits like improved student graduation rates or reduced costs associated with unaddressed mental health issues (e.g., the cost of a suicide in the military).  
* **Addressing Therapist Concerns:** Therapists may initially fear replacement by AI. Emphasize that HumorHealer can address the severe demand-supply gap by handling "easy cases" and acting as a pre-screening or triage tool, freeing up therapists for more serious or complex cases. The system could "flag" concerning conversations for human intervention, acting as a human-in-the-loop system.  
* **Technology and Data Management:**  
  * **HIPAA Compliance:** If handling protected health information (PHI), HIPAA compliance is crucial. This means using HIPAA-compliant hosting (e.g., AWS, Google Cloud with specific settings, which can be 10x more expensive) and having Business Associate Agreements (BAAs) with any third-party services that could access data (e.g., texting APIs like Twilio if they can read messages). End-to-end encryption and robust cybersecurity procedures are essential.  
  * **Local Hosting:** For initial development, "do the minimum thing for now" regarding infrastructure. Scaling can be addressed when it becomes a "good problem to have."  
  * **Speech and Text Integration:** Utilize OpenAI's Whisper for human-like speech and Twilio for text and voice interactions.  
  * **Ethical AI:** HumorHealer needs robust safety guardrails. Responses should provide relevant options and suggestions rather than direct commands, especially given liability concerns in a school setting (e.g., "consider/suggest/think about" instead of "call this number"). It cannot diagnose in a school setting.  
  * **Data-Driven Insights:** The system can gather universal sentiment and difficulty analysis (e.g., if "shitty food" frequently appears in conversations on a submarine, it indicates a morale issue), providing anonymized data to institutions to address common problems. This "data gathering apparatus for morale" could be a significant value proposition for universities and the military.  
* **Patient Journey and User Experience:**  
  * **Accessibility:** HumorHealer addresses the desire for increased accessibility given long waiting lists for traditional therapy.  
  * **Self-Selection:** The ability for patients to self-select treatment or a "type" of humor/therapeutic approach is valuable.  
  * **Actionable Steps:** The AI should consolidate advice into small, actionable steps, much like a therapist.  
  * **Cultural Competence:** Training the model to understand cultural context is vital, as healing processes are culturally based.  
* **Funding and Legal:** Explore NSF/NIH I-CORP, SBIR/STTR grants (Phase 1: $250k, Phase 2: $1.5M; STTR requires non-profit collaboration). Seek legal advice on IP protection and licensing after initial prototype development. IRB approval can offer liability protections.

**Growth Opportunities:**

* **Partnerships:** Collaborate with mental health-conscious clubs and leverage JHU's Data Science and AI initiative for investment and compute resources. JHU-APL technology collaborations could be a significant avenue.  
* **Expansion:** Branch out from Johns Hopkins University to other institutions after initial success, including exploring military markets through specialists.  
* **Profile Building:** HumorHealer can continually tune itself to user humor preferences and build a profile based on interactions to provide more relevant responses, similar to a therapist's approach of offering actionable steps.

**Possibility of a Strategic Pivot to AI Educational Tutoring:**  
While the provided documents do not explicitly discuss a strategic pivot to AI educational tutoring, the core technology of customizable AI-powered chatbots and the experience in fine-tuning models (e.g., LORA, RAG, and fine-tuning on specific datasets for humor and therapeutic dialogue) are highly transferable. The team's background in physics, mathematics, biomedical engineering, and applied mathematics, along with extensive experience with large language models and a focus on understanding user needs and providing tailored support, suggests a strong technical and foundational capability for such a pivot. The ability to "filter" and "narrow down results to reduce stress and provide info in a focused way," as discussed for therapy, directly translates to an educational tutoring context where students often feel overwhelmed by information. The emphasis on ethical guidelines, user understanding, and providing actionable steps (similar to a therapist guiding a client) aligns well with the principles of effective educational support. Further research and customer discovery in the educational sector would be needed to assess the specific market opportunities and required adaptations for AI educational tutoring using their existing capabilities.

Additional Expert Insights from NSF I-Corps Business Idea Validation Program:

**Customer Discovery and Market Understanding:**

* **Interview Quantity for Insights:** Aim for 60-70 interviews to start seeing initial insights and patterns, and up to 100-150 interviews per segment on a national basis for more comprehensive understanding. This applies to potential users, buyers (e.g., university mental health authorities), and decision-makers in institutions. ( I-Corps Opening)  
* **Focus on Workflow and Pain Points:** During interviews, prioritize understanding the current workflow, how and when decisions are made, who is involved, and what resources are used. Identify clear impacts and consequences of current practices that HumorHealer could address, such as long waiting lists for therapy, lack of therapist availability, or cost barriers. ( I-Corps Opening)  
* **Avoid Product Bias:** Frame questions to learn about what makes mental health technology successful from the interviewee's perspective, rather than directly asking about or biasing them towards HumorHealer. ( ICORP Questions, I-Corps Opening)  
* **Identifying the "Job-to-be-Done":** Understand what "job" customers would "hire" HumorHealer to do, what solutions they are currently using, and why they would switch. People care about progress, not just products. ( I-Corps Opening)  
* **Quantifying Value in Industry:** Consider metrics like Quality-Adjusted Life Years (QALYs) to quantify the value proposition, especially when presenting to institutions. This helps in understanding the worth of extending life or improving utility levels through the introduction of new techniques. ( Closing Remarks)

**Addressing Therapist Concerns and Integration:**

* **AI as a Complement, not Replacement:** Emphasize that HumorHealer can address the severe demand-supply gap in mental health by handling "easy cases," acting as a pre-screening or triage tool, and freeing up therapists for more serious or complex cases. The system could "flag" concerning conversations for human intervention, functioning as a human-in-the-loop system. ( Aug 9, 2024 | Diksha, Aug 2, 2024 | Vitor Meeting \- Consulting, Aug 13, 2024 | Ed Dannettel Interview, Bradley Kuo Interview)  
* **Data-Driven Insights for Institutions:** HumorHealer can gather universal sentiment and difficulty analysis (e.g., identifying common issues like "shitty food" on a submarine affecting morale). This anonymized data can be a significant value proposition for universities and the military to address common problems and improve overall well-being. ( I-Corps Opening)  
* **"Flagging" and Intervention:** The system should be designed to highlight concerning problems or "tag" conversations for potential therapist intervention, especially if it is involved in a medical context. ( Aug 2, 2024 | Vitor Meeting \- Consulting)

**Technical and Data Management Considerations:**

* **HIPAA Compliance:** If handling Protected Health Information (PHI), HIPAA compliance is crucial. This entails using HIPAA-compliant hosting (e.g., AWS, Google Cloud with specific settings, which can be significantly more expensive) and having Business Associate Agreements (BAAs) with any third-party services (like texting APIs if they can read messages). End-to-end encryption and robust cybersecurity procedures are essential. ( Aug 2, 2024 | Vitor Meeting \- Consulting)  
* **"Do the Minimum Thing for Now":** For initial development, focus on essential infrastructure. Scaling can be addressed when it becomes a "good problem to have." ( Aug 2, 2024 | Vitor Meeting \- Consulting)  
* **Speech and Text Integration:** Utilize OpenAI's Whisper model for human-like speech and Twilio for text and voice interactions. ( Aug 2, 2024 | Vitor Meeting \- Consulting)  
* **Ethical AI and Liability:** HumorHealer needs robust safety guardrails. Responses should provide relevant options and suggestions ("consider/suggest/think about") rather than direct commands ("call this number"), especially in a school setting due to liability concerns. It cannot diagnose in a school setting. ( 8/7/24 \- Jacqueline Cochran)

**Patient Journey and User Experience:**

* **Addressing Accessibility and Waiting Lists:** HumorHealer directly addresses the widespread problem of long waiting lists for traditional therapy and the desire for increased accessibility. ( Aug 9, 2024 | Diksha, Bradley Kuo Interview, Aug 12, 2024 | Patrick Mitchell Interview, Aug 13, 2024 | Sandrine Pirard Interview)  
* **Self-Selection and Personalization:** The ability for patients to self-select treatment or a "type" of humor/therapeutic approach is a valuable feature. The AI should be able to adapt its humor to individual users. ( Bradley Kuo Interview, 8/13/24 \- Larry Hopwood)  
* **Actionable Steps:** The AI should consolidate advice into small, actionable steps, similar to how a human therapist would guide a client. ( 8/7/24 \- Jacqueline Cochran)  
* **Cultural Competence:** Training the model to understand cultural context is vital, as healing processes are often culturally based. ( Bradley Kuo Interview, Aug 14, 2024 | SAM INTERVIEW)  
* **Comfort and Trust:** The anonymity and non-judgmental nature of a chatbot can make it easier for individuals, especially those in early stages of addressing issues, to talk about their struggles without fear of judgment. ( Aug 13, 2024 | Ed Dannettel Interview, 8/22/24 \- Saumya Singh)

**Funding and Legal:**

* **Grant Opportunities:** Explore NSF/NIH I-CORP and SBIR/STTR grants (Phase 1: $250k, Phase 2: $1.5M; STTR requires non-profit collaboration). ( Closing Remarks)  
* **IP Protection and Licensing:** Seek legal advice on IP protection and licensing after initial prototype development. ( 8/14/24 \- Sephora)  
* **IRB Approval:** Obtaining Institutional Review Board (IRB) approval can offer liability protections. ( Aug 2, 2024 | Vitor Meeting \- Consulting)

**Growth Opportunities:**

* **JHU-APL Technology Collaborations:** Leverage the potential for technology collaborations with the Johns Hopkins University Applied Physics Laboratory (JHU-APL). ( Aug 13, 2024 | Ed Dannettel Interview)

Sources:

* [Aug 13, 2024 | Sandrine Pirard Interview](https://drive.google.com/open?id=15xm3diRUZ_VsmRYBMkZGlD4ER9AYjNOKtssrxyGtKOM)  
* [Meeting notes](https://drive.google.com/open?id=1og0BjnQC4mRAWqyKmw_pZx8qaxO-gmFlWjJ8bwd6utU)  
* [Bradley Kuo Interview](https://drive.google.com/open?id=1WHKS9VTm6CxpuXPmpLCTSV3yXsoH7yd5HnnvfqcZbIw)  
* [Aug 13, 2024 | Ed Dannettel Interview](https://drive.google.com/open?id=1belHzQDqOqX5C8mu2yuLAk7RD3mFF6obD3XeW52ro6Y)  
* [I-Corps @ JHU](https://drive.google.com/open?id=1yWOHuOyl8BntiO7VhLs3a4vsABUVmGKj)  
* [8/15/24 \- Estevan Pina](https://drive.google.com/open?id=1mV55Kxm2ysb_FIIN-ZdTLM9svuaIk1bnu-8eFpIUcyA)  
* [8/22/24 \- Saumya Singh](https://drive.google.com/open?id=1wD1WVSSfeFRRUWbA3G4OOaOHe4Qo-Sfp3d3pBw6SkHs)  
* [Aug 12, 2024 | Patrick Mitchell Interview](https://drive.google.com/open?id=1TpNgCBNRg0lNAoW21Cf9QP9tOXmVT1yGz_p4XLW1STM)  
* [8/12/2024 \- Pat Mitchell](https://drive.google.com/open?id=16rF4nx3md98xKVgnJW18r1QdIXqTjyBdjxuvvEDOh-k)  
* [Aug 2, 2024 | Vitor Meeting \- Consulting](https://drive.google.com/open?id=1AHf--BwwvPnMvfFmNTaSdU86yH8OWfCv0BOJrsM4W5U)  
* [ICORP Contact List](https://drive.google.com/open?id=1Z75Wl7UB0i-_9RsVQV59eVutx4GakTSLQXE-M7WXX9o)  
* [8/14/24 \- Hadley VanRenterghem](https://drive.google.com/open?id=1pnM3R-KXp8lMqEcn-P9YepoDxJCOywBfIBPgXXx2h3Q)  
* [Closing Remarks](https://drive.google.com/open?id=1MjUIkk5AAOa1U9tHRu54YBDvrQI5jm-by289n9Ggvyg)  
* [Gemini Export June 23, 2025 at 7:05:17 AM EDT](https://docs.google.com/document/d/1G5JZJpGar1-r1Xv0C93oPIGUgekyMGwb0j-zO1EQIds/edit)  
* [ICORP Questions](https://drive.google.com/open?id=1DPu3noKjlnQC30BbqVprZY9uV0KoBAXDLcfQ6ZWgPpI)  
* [Aug 13, 2024 | Graham Interview](https://drive.google.com/open?id=1x-9sJemmP1lXx4F_eNK9V_wTGxlIwEBrcH5w3y2B7T8)  
* [I-Corps Opening](https://drive.google.com/open?id=1-foLKk0Zt_6d3ci0mZAbHd9dgqOzsCmMSHXnEptyHkE)  
* [ICORP Phone script](https://drive.google.com/open?id=1HK6w7LJNWWb0CQ1P-XWg0S9VwxCI0Ogt8Ot5RMCXt68)  
* [ICORP Feedback](https://drive.google.com/open?id=1geZfMZ6hp177o6KRCL7iB4P_eS63x--FtzaJwQeW9Ks)  
* [8/7/24 \- Jacqueline Cochran](https://drive.google.com/open?id=1hCcuBkByzu0Xw9eT8gYySAdZTEnDphtEe3F9H8z-nuU)  
* [8/14/24 \- Sephora](https://drive.google.com/open?id=1Bxa_--b912D-oy5bV95qQ3qExCRyZBRbF_Jdr-j7fhM)  
* [8/13/24 \- Larry Hopwood](https://drive.google.com/open?id=1PND3go2rtX2tZcoXZHAUHblVPnDBKifcc2L2b_O04_E)  
* [Aug 14, 2024 | SAM INTERVIEW](https://drive.google.com/open?id=1lSvsMDuwYNua2RslDiHX65FcDQXBPc4ccstiiea-Trk)  
* [Aug 9, 2024 | Diksha](https://drive.google.com/open?id=1R9uSryQOeWTFxrjAc9Qx5UmnuBew2WuUFmaWIRskQ4g)

Sources:

* [I-Corps @ JHU](https://drive.google.com/open?id=1yWOHuOyl8BntiO7VhLs3a4vsABUVmGKj)