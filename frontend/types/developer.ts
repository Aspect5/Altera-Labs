// Developer-related types
export interface DeveloperConfig {
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

export interface LLMAttempt {
  attempt: number;
  tactic: string;
  leanError?: string;
  success: boolean;
  timestamp: string;
  proofState: string;
  error_info?: any;
}

export interface DeveloperLogs {
  developer_mode: boolean;
  max_auto_solve_attempts: number;
  config: DeveloperConfig;
  recent_logs: any[];
  attempt_logs: any[];
}

export interface LeanErrorInfo {
  type: string;
  message: string;
  line_number?: number;
  column_number?: number;
  suggestion?: string;
  context?: string;
} 