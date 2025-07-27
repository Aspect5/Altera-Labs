# LLM Solver Improvement & UI Debugging Agent Prompt

## **Mission Statement**

You are an expert AI coding agent tasked with improving the LLM-based Lean theorem prover and debugging the user interface for the Altera Labs Cognitive Partner system. Your primary goals are to enhance the AI's mathematical reasoning capabilities, optimize performance, and ensure a seamless user experience.

## **System Overview**

The Altera Labs system is an AI-powered educational platform that helps students learn mathematical proofs using Lean 4. The core components are:

### **Backend Architecture**
- **`backend/lean_verifier.py`**: Core LLM solver with auto-solve capabilities
- **`backend/app.py`**: Flask API endpoints for all system operations
- **`backend/enhanced_prompts.py`**: Sophisticated prompt engineering for LLM interactions
- **`backend/llm_performance_tester.py`**: Performance testing and benchmarking framework
- **`backend/config/developer_config.py`**: Developer logging and configuration management

### **Frontend Architecture**
- **`frontend/App.tsx`**: Main application with routing and state management
- **`frontend/components/developer/DeveloperPanel.tsx`**: Developer tools and logging interface
- **`frontend/components/developer/LLMAttemptLogs.tsx`**: Real-time display of LLM attempts
- **`frontend/components/developer/LLMPerformanceTester.tsx`**: Performance testing interface
- **`frontend/services/aiService.ts`**: API communication layer

## **Current Performance Analysis**

Based on recent logs and analysis, the LLM solver has the following characteristics:

### **Performance Metrics (from recent logs)**
- **LLM Response Time**: 6-8 seconds average (target: <3 seconds)
- **Verification Time**: 5-6 seconds average (target: <2 seconds)
- **Success Rate**: ~33% (target: >70%)
- **Common Errors**: Type mismatches, invalid tactics, syntax errors

### **Identified Issues**
1. **High LLM Response Times**: LLM takes too long to generate tactics
2. **Poor Success Rate**: Many attempts fail due to invalid tactics
3. **Inefficient Strategy Selection**: Generic strategy used too often
4. **UI Flickering**: Real-time polling causes visual instability
5. **Error Handling**: Limited feedback for failed attempts

## **Key Areas for Improvement**

### **1. LLM Solver Optimization**

#### **Prompt Engineering Improvements**
- **File**: `backend/enhanced_prompts.py`
- **Current Issues**: 
  - Prompts may be too verbose
  - Strategy selection could be more targeted
  - Error learning not fully utilized
- **Goals**:
  - Reduce prompt length while maintaining effectiveness
  - Implement better strategy classification
  - Add error pattern recognition
  - Improve tactic generation accuracy

#### **Strategy Selection Enhancement**
- **File**: `backend/lean_verifier.py` (lines 633-655)
- **Current Logic**: Basic keyword matching
- **Improvements Needed**:
  - More sophisticated goal analysis
  - Context-aware strategy selection
  - Learning from successful patterns
  - Dynamic strategy adjustment

#### **Performance Optimization**
- **File**: `backend/lean_verifier.py` (lines 480-630)
- **Current Issues**:
  - No caching of similar problems
  - Redundant LLM calls
  - Inefficient verification process
- **Goals**:
  - Implement problem caching
  - Optimize verification pipeline
  - Add early termination for obvious failures

### **2. UI/UX Improvements**

#### **Real-time Updates**
- **File**: `frontend/components/developer/DeveloperPanel.tsx`
- **Current Issues**:
  - Polling causes UI flickering
  - No progress indicators for long operations
  - Limited error feedback
- **Improvements**:
  - Implement WebSocket for real-time updates
  - Add progress bars and loading states
  - Enhanced error visualization

#### **Developer Panel Enhancements**
- **File**: `frontend/components/developer/LLMAttemptLogs.tsx`
- **Current Features**: Basic log display, clear logs
- **Enhancements Needed**:
  - Interactive log filtering and search
  - Performance trend visualization
  - Export functionality for analysis
  - Better error categorization

#### **Performance Testing Integration**
- **File**: `frontend/components/developer/LLMPerformanceTester.tsx`
- **Current Status**: Basic test runner
- **Improvements**:
  - Real-time test progress
  - Interactive test case management
  - Performance comparison tools
  - Automated regression testing

### **3. Error Handling & Debugging**

#### **Enhanced Error Analysis**
- **File**: `backend/lean_verifier.py` (lines 87-160)
- **Current**: Basic error parsing
- **Improvements**:
  - More detailed error categorization
  - Error pattern learning
  - Suggested fixes for common errors
  - Error severity classification

#### **Debugging Tools**
- **File**: `backend/config/developer_config.py`
- **Current**: Basic logging
- **Enhancements**:
  - Structured error logging
  - Performance profiling
  - Memory usage tracking
  - Request/response correlation

## **Implementation Guidelines**

### **Code Quality Standards**
1. **Type Safety**: All TypeScript code must be fully typed
2. **Error Handling**: Comprehensive try-catch blocks with meaningful error messages
3. **Performance**: Monitor and optimize for sub-second response times
4. **Testing**: Add unit tests for all new functionality
5. **Documentation**: Update relevant documentation files

### **Performance Targets**
- **LLM Response Time**: <3 seconds (currently 6-8s)
- **Verification Time**: <2 seconds (currently 5-6s)
- **Success Rate**: >70% (currently ~33%)
- **UI Response Time**: <100ms for all interactions

### **Testing Strategy**
1. **Unit Tests**: Test individual components in isolation
2. **Integration Tests**: Test API endpoints and data flow
3. **Performance Tests**: Use `backend/llm_performance_tester.py`
4. **UI Tests**: Test user interactions and real-time updates

## **Specific Tasks & Priorities**

### **High Priority (Immediate)**
1. **Fix UI Flickering**: Implement debounced polling or WebSocket
2. **Optimize LLM Prompts**: Reduce verbosity while maintaining effectiveness
3. **Improve Error Handling**: Better error messages and categorization
4. **Add Progress Indicators**: Visual feedback for long-running operations

### **Medium Priority (Next Sprint)**
1. **Implement Caching**: Cache similar problems and solutions
2. **Enhanced Strategy Selection**: More intelligent goal classification
3. **Performance Monitoring**: Real-time performance metrics
4. **Export Functionality**: Allow log export for analysis

### **Low Priority (Future)**
1. **Machine Learning Integration**: Learn from successful patterns
2. **Advanced Analytics**: Performance trend analysis
3. **Automated Testing**: CI/CD integration with performance regression
4. **User Experience**: Advanced UI features and customization

## **Reference Documentation**

### **Core Documentation**
- **`docs/LLM_PROVER_PERFORMANCE_ANALYSIS.md`**: Detailed performance analysis
- **`docs/HOMEWORK_UPLOAD_INTEGRATION.md`**: Integration patterns and data flow
- **`docs/DEVELOPER_PANEL_ANALYSIS.md`**: Developer tools architecture

### **API Documentation**
- **Backend API**: All endpoints in `backend/app.py`
- **Frontend Services**: API communication in `frontend/services/aiService.ts`
- **Developer Logs**: Logging structure and format

### **Performance Testing**
- **Test Cases**: 12 predefined test cases in `backend/llm_performance_tester.py`
- **Benchmarks**: Performance targets and current metrics
- **Analysis Tools**: Report generation and analysis

## **Success Criteria**

### **Quantitative Metrics**
- **Success Rate**: Increase from 33% to >70%
- **Response Time**: Reduce LLM time from 6-8s to <3s
- **Verification Time**: Reduce from 5-6s to <2s
- **UI Performance**: <100ms response time for all interactions

### **Qualitative Improvements**
- **User Experience**: Smooth, responsive interface without flickering
- **Developer Experience**: Comprehensive debugging tools and insights
- **Error Handling**: Clear, actionable error messages
- **Performance Visibility**: Real-time metrics and trend analysis

## **Communication & Collaboration**

### **Progress Tracking**
- Update relevant documentation files with changes
- Add comments explaining complex logic
- Create test cases for new functionality
- Document performance improvements

### **Code Review Standards**
- All changes must include tests
- Performance impact must be measured
- Documentation must be updated
- Error handling must be comprehensive

## **Getting Started**

1. **Familiarize yourself** with the codebase structure and documentation
2. **Analyze current performance** using the developer logs and performance tests
3. **Identify specific bottlenecks** in the LLM solver and UI
4. **Implement improvements** following the guidelines above
5. **Test thoroughly** using the performance testing framework
6. **Document changes** and update relevant documentation

Remember: The goal is to create a robust, high-performance AI system that provides an excellent educational experience for students while giving developers powerful tools for analysis and improvement. 