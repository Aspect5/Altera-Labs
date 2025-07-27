// frontend/components/developer/ConfigPanel.tsx

import React, { useState } from 'react';

interface DeveloperConfig {
  developer_mode: boolean;
  max_auto_solve_attempts: number;
  log_level: string;
  enable_detailed_logging: boolean;
  save_attempt_logs: boolean;
  auto_save_interval: number;
  max_log_entries: number;
  lean_timeout: number;
  enable_error_parsing: boolean;
  enable_llm_feedback: boolean;
}

interface ConfigPanelProps {
  config: DeveloperConfig | null;
  isLoading: boolean;
  onToggleDeveloperMode: (enabled: boolean, maxAttempts?: number) => Promise<void>;
  onRefresh: () => void;
}

export const ConfigPanel: React.FC<ConfigPanelProps> = ({
  config,
  isLoading,
  onToggleDeveloperMode,
  onRefresh
}) => {
  const [isUpdating, setIsUpdating] = useState(false);
  const [localConfig, setLocalConfig] = useState<Partial<DeveloperConfig>>({});
  const [showAdvanced, setShowAdvanced] = useState(false);

  // Initialize local config when config prop changes
  React.useEffect(() => {
    if (config) {
      setLocalConfig(config);
    }
  }, [config]);

  const handleToggleDeveloperMode = async (enabled: boolean) => {
    try {
      setIsUpdating(true);
      await onToggleDeveloperMode(enabled, localConfig.max_auto_solve_attempts);
    } catch (error) {
      console.error('Failed to toggle developer mode:', error);
    } finally {
      setIsUpdating(false);
    }
  };

  const handleMaxAttemptsChange = (value: number) => {
    setLocalConfig(prev => ({ ...prev, max_auto_solve_attempts: value }));
  };

  const handleConfigChange = (key: keyof DeveloperConfig, value: any) => {
    setLocalConfig(prev => ({ ...prev, [key]: value }));
  };

  const handleSaveConfig = async () => {
    try {
      setIsUpdating(true);
      await onToggleDeveloperMode(
        localConfig.developer_mode ?? false,
        localConfig.max_auto_solve_attempts
      );
    } catch (error) {
      console.error('Failed to save configuration:', error);
    } finally {
      setIsUpdating(false);
    }
  };

  if (isLoading) {
    return (
      <div className="flex items-center justify-center h-full">
        <div className="text-slate-400">Loading configuration...</div>
      </div>
    );
  }

  return (
    <div className="h-full flex flex-col p-4">
      {/* Header */}
      <div className="flex items-center justify-between mb-4">
        <h3 className="text-lg font-semibold text-white">Developer Configuration</h3>
        <button
          onClick={onRefresh}
          className="px-3 py-1 bg-slate-700 hover:bg-slate-600 text-white rounded text-sm transition-colors"
        >
          Refresh
        </button>
      </div>

      {/* Main Configuration */}
      <div className="flex-1 overflow-y-auto space-y-6">
        {/* Developer Mode Toggle */}
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-4">
          <div className="flex items-center justify-between mb-4">
            <div>
              <h4 className="text-white font-medium">Developer Mode</h4>
              <p className="text-sm text-slate-400">
                Enable advanced debugging and logging features
              </p>
            </div>
            <button
              onClick={() => handleToggleDeveloperMode(!(localConfig.developer_mode ?? false))}
              disabled={isUpdating}
              className={`relative inline-flex h-6 w-11 items-center rounded-full transition-colors ${
                localConfig.developer_mode ? 'bg-blue-600' : 'bg-slate-600'
              }`}
            >
              <span
                className={`inline-block h-4 w-4 transform rounded-full bg-white transition-transform ${
                  localConfig.developer_mode ? 'translate-x-6' : 'translate-x-1'
                }`}
              />
            </button>
          </div>
          
          {localConfig.developer_mode && (
            <div className="space-y-3">
              <div>
                <label className="block text-sm font-medium text-slate-300 mb-1">
                  Max Auto-Solve Attempts
                </label>
                <input
                  type="number"
                  min="1"
                  max="20"
                  value={localConfig.max_auto_solve_attempts ?? 5}
                  onChange={(e) => handleMaxAttemptsChange(parseInt(e.target.value))}
                  className="w-full px-3 py-2 bg-slate-700 border border-slate-600 text-white rounded focus:outline-none focus:ring-2 focus:ring-blue-500"
                />
                <p className="text-xs text-slate-400 mt-1">
                  Maximum number of attempts for AI auto-solving (1-20)
                </p>
              </div>
            </div>
          )}
        </div>

        {/* Auto-Solve Configuration */}
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-4">
          <h4 className="text-white font-medium mb-3">Auto-Solve Settings</h4>
          <div className="space-y-3">
            <div>
              <label className="block text-sm font-medium text-slate-300 mb-1">
                Lean Timeout (seconds)
              </label>
              <input
                type="number"
                min="5"
                max="120"
                value={localConfig.lean_timeout ?? 30}
                onChange={(e) => handleConfigChange('lean_timeout', parseInt(e.target.value))}
                className="w-full px-3 py-2 bg-slate-700 border border-slate-600 text-white rounded focus:outline-none focus:ring-2 focus:ring-blue-500"
              />
            </div>
            
            <div>
              <label className="block text-sm font-medium text-slate-300 mb-1">
                Enable Error Parsing
              </label>
              <div className="flex items-center">
                <input
                  type="checkbox"
                  checked={localConfig.enable_error_parsing ?? true}
                  onChange={(e) => handleConfigChange('enable_error_parsing', e.target.checked)}
                  className="w-4 h-4 text-blue-600 bg-slate-700 border-slate-600 rounded focus:ring-blue-500"
                />
                <span className="ml-2 text-sm text-slate-300">
                  Parse Lean error output for better feedback
                </span>
              </div>
            </div>

            <div>
              <label className="block text-sm font-medium text-slate-300 mb-1">
                Enable LLM Feedback
              </label>
              <div className="flex items-center">
                <input
                  type="checkbox"
                  checked={localConfig.enable_llm_feedback ?? true}
                  onChange={(e) => handleConfigChange('enable_llm_feedback', e.target.checked)}
                  className="w-4 h-4 text-blue-600 bg-slate-700 border-slate-600 rounded focus:ring-blue-500"
                />
                <span className="ml-2 text-sm text-slate-300">
                  Use LLM to generate error suggestions
                </span>
              </div>
            </div>
          </div>
        </div>

        {/* Advanced Settings */}
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-4">
          <div className="flex items-center justify-between mb-3">
            <h4 className="text-white font-medium">Advanced Settings</h4>
            <button
              onClick={() => setShowAdvanced(!showAdvanced)}
              className="text-sm text-blue-400 hover:text-blue-300"
            >
              {showAdvanced ? 'Hide' : 'Show'} Advanced
            </button>
          </div>
          
          {showAdvanced && (
            <div className="space-y-3">
              <div>
                <label className="block text-sm font-medium text-slate-300 mb-1">
                  Log Level
                </label>
                <select
                  value={localConfig.log_level ?? 'INFO'}
                  onChange={(e) => handleConfigChange('log_level', e.target.value)}
                  className="w-full px-3 py-2 bg-slate-700 border border-slate-600 text-white rounded focus:outline-none focus:ring-2 focus:ring-blue-500"
                >
                  <option value="DEBUG">DEBUG</option>
                  <option value="INFO">INFO</option>
                  <option value="WARNING">WARNING</option>
                  <option value="ERROR">ERROR</option>
                </select>
              </div>

              <div>
                <label className="block text-sm font-medium text-slate-300 mb-1">
                  Enable Detailed Logging
                </label>
                <div className="flex items-center">
                  <input
                    type="checkbox"
                    checked={localConfig.enable_detailed_logging ?? true}
                    onChange={(e) => handleConfigChange('enable_detailed_logging', e.target.checked)}
                    className="w-4 h-4 text-blue-600 bg-slate-700 border-slate-600 rounded focus:ring-blue-500"
                  />
                  <span className="ml-2 text-sm text-slate-300">
                    Log detailed information for debugging
                  </span>
                </div>
              </div>

              <div>
                <label className="block text-sm font-medium text-slate-300 mb-1">
                  Save Attempt Logs
                </label>
                <div className="flex items-center">
                  <input
                    type="checkbox"
                    checked={localConfig.save_attempt_logs ?? true}
                    onChange={(e) => handleConfigChange('save_attempt_logs', e.target.checked)}
                    className="w-4 h-4 text-blue-600 bg-slate-700 border-slate-600 rounded focus:ring-blue-500"
                  />
                  <span className="ml-2 text-sm text-slate-300">
                    Persist attempt logs to disk
                  </span>
                </div>
              </div>

              <div>
                <label className="block text-sm font-medium text-slate-300 mb-1">
                  Auto-Save Interval (seconds)
                </label>
                <input
                  type="number"
                  min="5"
                  max="300"
                  value={localConfig.auto_save_interval ?? 30}
                  onChange={(e) => handleConfigChange('auto_save_interval', parseInt(e.target.value))}
                  className="w-full px-3 py-2 bg-slate-700 border border-slate-600 text-white rounded focus:outline-none focus:ring-2 focus:ring-blue-500"
                />
              </div>

              <div>
                <label className="block text-sm font-medium text-slate-300 mb-1">
                  Max Log Entries
                </label>
                <input
                  type="number"
                  min="100"
                  max="10000"
                  value={localConfig.max_log_entries ?? 1000}
                  onChange={(e) => handleConfigChange('max_log_entries', parseInt(e.target.value))}
                  className="w-full px-3 py-2 bg-slate-700 border border-slate-600 text-white rounded focus:outline-none focus:ring-2 focus:ring-blue-500"
                />
              </div>
            </div>
          )}
        </div>

        {/* Current Status */}
        <div className="bg-slate-800 border border-slate-700 rounded-lg p-4">
          <h4 className="text-white font-medium mb-3">Current Status</h4>
          <div className="grid grid-cols-2 gap-4 text-sm">
            <div>
              <span className="text-slate-400">Developer Mode:</span>
              <span className={`ml-2 ${localConfig.developer_mode ? 'text-green-400' : 'text-red-400'}`}>
                {localConfig.developer_mode ? 'Enabled' : 'Disabled'}
              </span>
            </div>
            <div>
              <span className="text-slate-400">Max Attempts:</span>
              <span className="ml-2 text-white">{localConfig.max_auto_solve_attempts ?? 5}</span>
            </div>
            <div>
              <span className="text-slate-400">Log Level:</span>
              <span className="ml-2 text-white">{localConfig.log_level ?? 'INFO'}</span>
            </div>
            <div>
              <span className="text-slate-400">Lean Timeout:</span>
              <span className="ml-2 text-white">{localConfig.lean_timeout ?? 30}s</span>
            </div>
          </div>
        </div>
      </div>

      {/* Save Button */}
      <div className="mt-4 pt-4 border-t border-slate-700">
        <button
          onClick={handleSaveConfig}
          disabled={isUpdating}
          className="w-full px-4 py-2 bg-blue-600 hover:bg-blue-500 disabled:bg-blue-800 text-white rounded-lg transition-colors"
        >
          {isUpdating ? 'Saving...' : 'Save Configuration'}
        </button>
      </div>
    </div>
  );
}; 