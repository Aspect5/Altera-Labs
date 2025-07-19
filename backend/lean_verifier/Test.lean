import Mathlib.Data.Real.Basic

theorem test_theorem : ∃ x : ℝ, x > 0 := by
  use 1
  norm_num
