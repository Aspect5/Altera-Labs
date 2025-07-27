# **AI SWE IMPLEMENTATION PROMPT: CRITICAL GAPS 1, 2, & 3**

## **🎯 MISSION**

You are an AI Software Engineer tasked with implementing three critical gaps in the Altera Labs AI Cognitive Partner application. This is a React + Flask AI tutoring system focused on mathematical verifiability via Lean 4 and Bayesian Knowledge Tracing (BKT).

## **📋 CONTEXT & GOALS**

### **Core Application Purpose**
- **Primary Goal**: Create a pedagogically superior AI tutor that prevents cognitive offloading while promoting cognitive partnership
- **Mathematical Focus**: Group theory with Lean 4 verification
- **Pedagogical Approach**: Socratic tutoring (guide, don't give answers)
- **Student Modeling**: Bayesian Knowledge Tracing for personalized learning

### **Current State**
- ✅ Dashboard system with class health scores and plant states
- ✅ Gamification framework (achievements, points, levels, streaks)
- ✅ Knowledge visualization with D3.js
- ✅ Modular TypeScript architecture
- ✅ Flask backend with session management
- ❌ **GAP 1**: Gamification not connected to main learning flow
- ❌ **GAP 2**: Session management broken, class creation issues
- ❌ **GAP 3**: Lean 4 verification not functional

## **🔧 IMPLEMENTATION TASKS**

### **GAP 1: GAMIFICATION INTEGRATION** (Priority: HIGH)

#### **Objective**
Connect the built gamification system to the main learning flow to provide motivation and prevent cognitive offloading.

#### **Key Files to Examine**
1. `frontend/App.tsx` - Main application state management
2. `frontend/services/gamificationService.ts` - Gamification backend logic
3. `frontend/types.ts` - TypeScript type definitions
4. `frontend/src/pages/TutorPage.tsx` - Main learning interface
5. `frontend/components/gamification/AchievementSystem.tsx` - Achievement display
6. `frontend/components/learning/ProgressFlowers.tsx` - Visual progress indicators
7. `frontend/components/chat/MoodIndicator.tsx` - Affective state display

#### **Implementation Steps**
1. **Add gamification state to App.tsx**
   - Import `gamificationService` and `GamificationState` type
   - Add state variables for `gamificationState`, `affectiveState`, `confidence`
   - Initialize with `gamificationService.getState()`

2. **Create gamification trigger functions**
   - `awardPoints(action, amount)` - Award points for learning actions
   - `updateAffectiveState(aiResponse)` - Update mood based on AI responses
   - `checkConceptMastery()` - Check for achievement unlocks

3. **Connect to learning actions**
   - Award 5 points for each chat interaction
   - Award 20 points for session completion
   - Award 25 points for concept mastery
   - Award 50 points for proof completion

4. **Pass props to TutorPage**
   - Add gamification props to TutorPage component
   - Display ProgressFlowers, MoodIndicator, AchievementSystem

#### **Verification Checklist**
- [ ] Points awarded for all learning interactions
- [ ] Achievements unlock at correct thresholds
- [ ] Visual feedback (progress flowers, mood indicators) visible
- [ ] Gamification state persists across browser sessions
- [ ] Affective state updates based on AI responses

### **GAP 2: AI SESSION MANAGEMENT** (Priority: HIGH)

#### **Objective**
Fix session flow and class creation to provide seamless user experience.

#### **Key Files to Examine**
1. `frontend/src/pages/SetupPage.tsx` - Class creation interface
2. `frontend/App.tsx` - Session state management
3. `frontend/src/pages/TutorPage.tsx` - Session navigation
4. `backend/app.py` - Backend session endpoints
5. `frontend/services/aiService.ts` - AI service layer

#### **Implementation Steps**
1. **Fix class creation in SetupPage.tsx**
   - Replace JSON with FormData for file uploads
   - Use `fetch('/api/add_class', { method: 'POST', body: formData })`
   - Handle syllabus and homework file uploads properly

2. **Add session state management to App.tsx**
   - Add `sessionId`, `sessionMode` state variables
   - Implement `saveSessionState()` and `loadSessionState()` functions
   - Use localStorage for session persistence

3. **Update handleSelectClass**
   - Call `startSession('homework')` when class is selected
   - Load class data from `dashboardService.getClassData(classId)`
   - Set session mode and hide dashboard

4. **Add session navigation to TutorPage**
   - Add "Back to Dashboard" button
   - Display current session mode and class name
   - Clear session indicators

#### **Verification Checklist**
- [ ] Class creation works with file uploads (syllabus/homework)
- [ ] Seamless transition from dashboard to chat
- [ ] Session state persists across page reloads
- [ ] Clear navigation between dashboard and chat
- [ ] Session ID properly managed
- [ ] Error handling for failed sessions

### **GAP 3: LEAN 4 VERIFICATION** (Priority: HIGH)

#### **Objective**
Activate actual Lean 4 verification for mathematical problems.

#### **Key Files to Examine**
1. `backend/lean_verifier/LeanVerifier.lean` - Lean 4 project files
2. `backend/lean_verifier/lakefile.toml` - Lean 4 build configuration
3. `backend/socratic_auditor.py` - AI interaction logic
4. `backend/app.py` - Chat endpoint integration
5. `backend/lean_verifier/LeanVerifier/Basic.lean` - Basic theorems

#### **Implementation Steps**
1. **Add group theory theorems to LeanVerifier.lean**
   - Add basic subgroup theorems
   - Add identity and inverse theorems
   - Ensure proper imports and syntax

2. **Implement ProvingAgent class in socratic_auditor.py**
   - Create `ProvingAgent` class with `solve_problem()` method
   - Implement `convert_to_lean()` for natural language conversion
   - Add `verify_with_lean()` using subprocess to run Lean 4
   - Add `generate_solution_graph()` for concept extraction

3. **Integrate with chat system in app.py**
   - Add `contains_math()` helper function
   - Modify chat endpoint to use ProvingAgent
   - Handle SOLVED/FAILED/ERROR states
   - Provide meaningful feedback for each state

4. **Test Lean 4 integration**
   - Verify Lean 4 project builds correctly
   - Test basic group theory problem verification
   - Ensure error handling for timeouts and failures

#### **Verification Checklist**
- [ ] Lean 4 project builds and runs correctly
- [ ] Basic group theory problems verified successfully
- [ ] Proving Agent provides meaningful feedback for failures
- [ ] Solution graphs generated for successful proofs
- [ ] Mathematical content in chat triggers verification
- [ ] Error handling for Lean 4 timeouts and failures

## **🔍 CRITICAL VERIFICATION POINTS**

### **Import Path Issues**
**VERIFY**: Check all import paths in learning components:
- `frontend/components/learning/StudentMasteryPanel.tsx` line 3
- `frontend/components/learning/StudentKnowledgeVector.tsx` line 3

These files have incorrect import paths for `bayesianService`. They should use:
```typescript
import { calculateMasteryProbability } from "../../services/bayesianService";
```

### **Backend Startup Issues**
**VERIFY**: Backend has import issues. Check:
- `backend/app.py` line 19: `from . import prompts`
- This should be `import prompts` (not relative import)

### **Service Integration**
**VERIFY**: All services are properly exported in:
- `frontend/services/index.ts`
- `frontend/components/index.ts`

### **Type Definitions**
**VERIFY**: All gamification types exist in:
- `frontend/types.ts` - Check for `GamificationState`, `Achievement` interfaces

## **🧪 TESTING REQUIREMENTS**

### **Before Implementation**
1. **Verify current build status**
   ```bash
   cd frontend && npm run build
   cd backend && python -m app
   ```

2. **Check existing functionality**
   - Dashboard loads correctly
   - Class health cards display
   - Backend API endpoints respond

### **After Each Gap Implementation**
1. **Gamification Integration**
   - Test points awarded for chat interactions
   - Verify achievements unlock
   - Check visual feedback displays

2. **Session Management**
   - Test class creation with file uploads
   - Verify session persistence
   - Check navigation flow

3. **Lean 4 Verification**
   - Test basic group theory problems
   - Verify Proving Agent responses
   - Check error handling

### **Final Integration Test**
1. **Complete user journey**
   - Create class → Start session → Chat interaction → Gamification triggers → Lean verification
2. **Cross-browser compatibility**
3. **Performance testing**

## **🚨 CRITICAL CONSIDERATIONS**

### **Error Handling**
- Always implement proper error handling for API calls
- Provide fallback behavior for gamification failures
- Handle Lean 4 timeouts gracefully

### **Performance**
- Use React.memo for gamification components
- Optimize state updates to prevent unnecessary re-renders
- Implement proper cleanup for session state

### **User Experience**
- Start gamification subtle, allow disabling
- Provide clear visual indicators for session state
- Give helpful feedback for mathematical verification failures

### **Code Quality**
- Maintain TypeScript type safety
- Follow existing code patterns and naming conventions
- Add appropriate comments for complex logic

## **📚 REFERENCE DOCUMENTS**

### **Implementation Documents**
- `IMPLEMENTATION_PLAN.md` - Detailed plan with code examples
- `TECHNICAL_SPEC.md` - Specific technical specifications
- `IMPLEMENTATION_SUMMARY.md` - Executive summary and timeline

### **Architecture Documents**
- `frontend/ARCHITECTURE.md` - Frontend architecture overview
- `frontend/components/README.md` - Component organization
- `README.md` - Project overview and setup

### **Research Context**
- `Information/PromptMaxing/Copy of Research Plan_ Lean 4 MVP.txt` - Core vision and goals

## **🎯 SUCCESS CRITERIA**

### **Gamification Integration**
- Points awarded for 100% of learning interactions
- Achievements unlock based on actual progress
- Visual feedback visible in all learning modes

### **Session Management**
- 100% successful class creation rate
- Seamless navigation between dashboard and chat
- Session state persists across interruptions

### **Lean 4 Verification**
- Basic group theory problems verified successfully
- Proving Agent provides meaningful feedback
- Mathematical content triggers verification

## **⚠️ IMPORTANT NOTES**

1. **Maintain Pedagogical Focus**: Every feature should support the goal of preventing cognitive offloading and promoting critical thinking
2. **Test Incrementally**: Implement and test each gap separately before moving to the next
3. **Preserve Existing Functionality**: Don't break working features while adding new ones
4. **Document Changes**: Update relevant documentation as you implement features
5. **Follow Best Practices**: Use TypeScript properly, handle errors gracefully, maintain clean code

## **🚀 IMPLEMENTATION ORDER**

1. **Start with Gap 1 (Gamification Integration)** - Foundation for motivation
2. **Then Gap 2 (Session Management)** - Fixes user experience
3. **Finally Gap 3 (Lean 4 Verification)** - Core mathematical functionality

Each gap builds on the previous one, so follow this order for optimal implementation.

**Remember**: You're building a pedagogically superior AI tutor that enhances critical thinking and metacognitive skills while preventing harmful cognitive offloading. Every decision should support this mission. 