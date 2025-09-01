import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
open Classical

theorem auto_proof : ∀ n : ℕ, n + 0 = n := by
  simp
