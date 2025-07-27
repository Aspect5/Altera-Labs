import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
open Classical

theorem arithmetic_opt : ∀ n m : ℕ, n + m = m + n := by intro n m; exact Nat.add_comm n m
