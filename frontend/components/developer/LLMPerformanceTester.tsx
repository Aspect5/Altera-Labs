import React, { useState, useEffect } from 'react';

interface TestCase {
  name: string;
  description: string;
  proof_state: string;
  expected_tactic?: string;
  difficulty: string;
  category: string;
  max_attempts: number;
}

interface TestResult {
  test_name: string;
  success: boolean;
  attempts_used: number;
  total_time: number;
  attempts: any[];
  final_proof: string;
  error_messages: string[];
  llm_response_quality: any;
}

interface PerformanceReport {
  filename: string;
  created: string;
  size: number;
}

interface TestSummary {
  total_tests: number;
  successful_tests: number;
  failed_tests: number;
  success_rate: number;
  average_attempts: number;
  average_time: number;
}

interface LLMQualityMetrics {
  total_responses: number;
  valid_tactics: number;
  invalid_tactics: number;
  valid_tactic_rate: number;
  markdown_formatted: number;
  natural_language_responses: number;
  empty_responses: number;
  average_response_length: number;
}

const LLMPerformanceTester: React.FC = () => {
  const [testCases, setTestCases] = useState<TestCase[]>([]);
  const [reports, setReports] = useState<PerformanceReport[]>([]);
  const [isRunningTests, setIsRunningTests] = useState(false);
  const [currentTest, setCurrentTest] = useState<string>('');
  const [testProgress, setTestProgress] = useState(0);
  const [testResults, setTestResults] = useState<TestResult[]>([]);
  const [summary, setSummary] = useState<TestSummary | null>(null);
  const [llmQuality, setLlmQuality] = useState<LLMQualityMetrics | null>(null);
  const [error, setError] = useState<string>('');
  const [success, setSuccess] = useState<string>('');

  useEffect(() => {
    loadTestCases();
    loadReports();
  }, []);

  const loadTestCases = async () => {
    try {
      const response = await fetch('/api/performance/test_cases');
      const data = await response.json();
      if (response.ok) {
        setTestCases(data.test_cases);
      } else {
        setError(data.error);
      }
    } catch (err) {
      setError('Failed to load test cases');
    }
  };

  const loadReports = async () => {
    try {
      const response = await fetch('/api/performance/reports');
      const data = await response.json();
      if (response.ok) {
        setReports(data.reports);
      } else {
        setError(data.error);
      }
    } catch (err) {
      setError('Failed to load reports');
    }
  };

  const runFullTestSuite = async () => {
    setIsRunningTests(true);
    setError('');
    setSuccess('');
    setTestProgress(0);
    setTestResults([]);
    setSummary(null);
    setLlmQuality(null);

    try {
      const response = await fetch('/api/performance/run_tests', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
      });

      const data = await response.json();
      
      if (response.ok) {
        setSummary(data.summary);
        setLlmQuality(data.llm_quality_metrics);
        setSuccess(`Test suite completed! Success rate: ${data.summary.success_rate.toFixed(1)}%`);
        loadReports(); // Refresh reports list
      } else {
        setError(data.error);
      }
    } catch (err) {
      setError('Failed to run test suite');
    } finally {
      setIsRunningTests(false);
      setTestProgress(100);
    }
  };

  const runSingleTest = async (testName: string) => {
    setCurrentTest(testName);
    setError('');
    setSuccess('');

    try {
      const response = await fetch('/api/performance/run_single_test', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ test_name: testName }),
      });

      const data = await response.json();
      
      if (response.ok) {
        setTestResults(prev => [...prev, data]);
        setSuccess(`Test '${testName}' completed: ${data.success ? 'SUCCESS' : 'FAILED'}`);
      } else {
        setError(data.error);
      }
    } catch (err) {
      setError(`Failed to run test '${testName}'`);
    } finally {
      setCurrentTest('');
    }
  };

  const downloadReport = async (filename: string) => {
    try {
      const response = await fetch(`/api/performance/download_report/${filename}`);
      const data = await response.json();
      
      if (response.ok) {
        // Create and download the file
        const blob = new Blob([data.content], { type: 'text/markdown' });
        const url = window.URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = filename;
        document.body.appendChild(a);
        a.click();
        window.URL.revokeObjectURL(url);
        document.body.removeChild(a);
      } else {
        setError(data.error);
      }
    } catch (err) {
      setError('Failed to download report');
    }
  };

  const getDifficultyColor = (difficulty: string) => {
    switch (difficulty) {
      case 'easy': return 'green';
      case 'medium': return 'yellow';
      case 'hard': return 'red';
      default: return 'gray';
    }
  };

  const getCategoryColor = (category: string) => {
    switch (category) {
      case 'arithmetic': return 'blue';
      case 'logic': return 'purple';
      case 'inequality': return 'orange';
      case 'advanced': return 'red';
      default: return 'gray';
    }
  };

  return (
    <div className="space-y-6">
      <div className="flex justify-between items-center">
        <h2 className="text-2xl font-bold text-gray-900">LLM Performance Testing</h2>
        <button
          onClick={runFullTestSuite}
          disabled={isRunningTests}
          className="bg-blue-600 hover:bg-blue-700 text-white px-4 py-2 rounded disabled:opacity-50"
        >
          {isRunningTests ? (
            <>
              <svg className="animate-spin w-4 h-4 mr-2 inline" fill="none" viewBox="0 0 24 24">
                <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4"></circle>
                <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"></path>
              </svg>
              Running Tests...
            </>
          ) : (
            'Run Full Test Suite'
          )}
        </button>
      </div>

      {error && (
        <div className="bg-red-50 border border-red-200 rounded-md p-4">
          <div className="flex justify-between items-start">
            <div>
              <h3 className="text-sm font-medium text-red-800">Error</h3>
              <p className="text-sm text-red-700 mt-1">{error}</p>
            </div>
            <button onClick={() => setError('')} className="text-red-400 hover:text-red-600">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>
        </div>
      )}

      {success && (
        <div className="bg-green-50 border border-green-200 rounded-md p-4">
          <div className="flex justify-between items-start">
            <div>
              <h3 className="text-sm font-medium text-green-800">Success</h3>
              <p className="text-sm text-green-700 mt-1">{success}</p>
            </div>
            <button onClick={() => setSuccess('')} className="text-green-400 hover:text-green-600">
              <svg className="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>
        </div>
      )}

      {isRunningTests && (
        <div className="bg-white shadow rounded-lg p-6">
          <div className="space-y-4">
            <h3 className="text-lg font-semibold">Test Progress</h3>
            <div className="w-full bg-gray-200 rounded-full h-2">
              <div 
                className="bg-blue-600 h-2 rounded-full transition-all duration-300" 
                style={{ width: `${testProgress}%` }}
              ></div>
            </div>
            <p className="text-sm text-gray-600">
              {currentTest ? `Running: ${currentTest}` : 'Preparing tests...'}
            </p>
          </div>
        </div>
      )}

      {/* Summary Results */}
      {summary && (
        <div className="bg-white shadow rounded-lg p-6">
          <h3 className="text-lg font-semibold mb-4">Test Summary</h3>
          <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
            <div className="text-center">
              <div className="text-2xl font-bold text-blue-600">{summary.total_tests}</div>
              <div className="text-sm text-gray-600">Total Tests</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-green-600">{summary.successful_tests}</div>
              <div className="text-sm text-gray-600">Successful</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-red-600">{summary.failed_tests}</div>
              <div className="text-sm text-gray-600">Failed</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-purple-600">{summary.success_rate.toFixed(1)}%</div>
              <div className="text-sm text-gray-600">Success Rate</div>
            </div>
          </div>
          <div className="mt-4 grid grid-cols-2 gap-4">
            <div className="text-center">
              <div className="text-lg font-semibold">{summary.average_attempts.toFixed(1)}</div>
              <div className="text-sm text-gray-600">Avg Attempts</div>
            </div>
            <div className="text-center">
              <div className="text-lg font-semibold">{summary.average_time.toFixed(2)}s</div>
              <div className="text-sm text-gray-600">Avg Time</div>
            </div>
          </div>
        </div>
      )}

      {/* LLM Quality Metrics */}
      {llmQuality && (
        <div className="bg-white shadow rounded-lg p-6">
          <h3 className="text-lg font-semibold mb-4">LLM Response Quality</h3>
          <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
            <div className="text-center">
              <div className="text-lg font-bold text-blue-600">{llmQuality.valid_tactic_rate.toFixed(1)}%</div>
              <div className="text-sm text-gray-600">Valid Tactics</div>
            </div>
            <div className="text-center">
              <div className="text-lg font-bold text-red-600">{llmQuality.markdown_formatted}</div>
              <div className="text-sm text-gray-600">Markdown Formatted</div>
            </div>
            <div className="text-center">
              <div className="text-lg font-bold text-orange-600">{llmQuality.natural_language_responses}</div>
              <div className="text-sm text-gray-600">Natural Language</div>
            </div>
            <div className="text-center">
              <div className="text-lg font-bold text-gray-600">{llmQuality.average_response_length.toFixed(0)}</div>
              <div className="text-sm text-gray-600">Avg Length</div>
            </div>
          </div>
        </div>
      )}

      {/* Test Cases */}
      <div className="bg-white shadow rounded-lg p-6">
        <h3 className="text-lg font-semibold mb-4">Available Test Cases ({testCases.length})</h3>
        <div className="space-y-3">
          {testCases.map((testCase) => (
            <div key={testCase.name} className="border rounded-lg p-4 hover:bg-gray-50">
              <div className="flex justify-between items-start">
                <div className="flex-1">
                  <div className="flex items-center gap-2 mb-2">
                    <h4 className="font-semibold">{testCase.name}</h4>
                    <span className={`px-2 py-1 text-xs rounded-full ${
                      getDifficultyColor(testCase.difficulty) === 'green' ? 'bg-green-100 text-green-800' :
                      getDifficultyColor(testCase.difficulty) === 'yellow' ? 'bg-yellow-100 text-yellow-800' :
                      getDifficultyColor(testCase.difficulty) === 'red' ? 'bg-red-100 text-red-800' :
                      'bg-gray-100 text-gray-800'
                    }`}>
                      {testCase.difficulty}
                    </span>
                    <span className={`px-2 py-1 text-xs rounded-full ${
                      getCategoryColor(testCase.category) === 'blue' ? 'bg-blue-100 text-blue-800' :
                      getCategoryColor(testCase.category) === 'purple' ? 'bg-purple-100 text-purple-800' :
                      getCategoryColor(testCase.category) === 'orange' ? 'bg-orange-100 text-orange-800' :
                      getCategoryColor(testCase.category) === 'red' ? 'bg-red-100 text-red-800' :
                      'bg-gray-100 text-gray-800'
                    }`}>
                      {testCase.category}
                    </span>
                  </div>
                  <p className="text-sm text-gray-600 mb-2">{testCase.description}</p>
                  <div className="text-xs font-mono bg-gray-100 p-2 rounded">
                    {testCase.proof_state}
                  </div>
                </div>
                <button
                  onClick={() => runSingleTest(testCase.name)}
                  disabled={isRunningTests || currentTest === testCase.name}
                  className="ml-4 px-3 py-1 text-sm bg-blue-600 text-white rounded hover:bg-blue-700 disabled:opacity-50"
                >
                  {currentTest === testCase.name ? (
                    <>
                      <svg className="animate-spin w-3 h-3 mr-1 inline" fill="none" viewBox="0 0 24 24">
                        <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4"></circle>
                        <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z"></path>
                      </svg>
                      Running
                    </>
                  ) : (
                    'Run Test'
                  )}
                </button>
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Individual Test Results */}
      {testResults.length > 0 && (
        <div className="bg-white shadow rounded-lg p-6">
          <h3 className="text-lg font-semibold mb-4">Individual Test Results</h3>
          <div className="space-y-3">
            {testResults.map((result, index) => (
              <div key={index} className="border rounded-lg p-4">
                <div className="flex items-center gap-2 mb-2">
                  <h4 className="font-semibold">{result.test_name}</h4>
                  <span className={`px-2 py-1 text-xs rounded-full ${
                    result.success ? 'bg-green-100 text-green-800' : 'bg-red-100 text-red-800'
                  }`}>
                    {result.success ? 'SUCCESS' : 'FAILED'}
                  </span>
                  <span className="text-sm text-gray-600">
                    {result.attempts_used} attempts, {result.total_time.toFixed(2)}s
                  </span>
                </div>
                <div className="text-xs font-mono bg-gray-100 p-2 rounded mb-2">
                  {result.final_proof}
                </div>
                {result.error_messages.length > 0 && (
                  <div className="text-sm text-red-600">
                    Errors: {result.error_messages.join(', ')}
                  </div>
                )}
              </div>
            ))}
          </div>
        </div>
      )}

      {/* Performance Reports */}
      <div className="bg-white shadow rounded-lg p-6">
        <h3 className="text-lg font-semibold mb-4">Performance Reports ({reports.length})</h3>
        {reports.length === 0 ? (
          <p className="text-gray-600">No reports available. Run a test suite to generate reports.</p>
        ) : (
          <div className="space-y-2">
            {reports.map((report) => (
              <div key={report.filename} className="flex justify-between items-center p-3 border rounded hover:bg-gray-50">
                <div>
                  <div className="font-medium">{report.filename}</div>
                  <div className="text-sm text-gray-600">
                    Created: {new Date(report.created).toLocaleString()}
                  </div>
                </div>
                <button
                  onClick={() => downloadReport(report.filename)}
                  className="px-3 py-1 text-sm bg-green-600 text-white rounded hover:bg-green-700"
                >
                  Download
                </button>
              </div>
            ))}
          </div>
        )}
      </div>
    </div>
  );
};

export default LLMPerformanceTester; 