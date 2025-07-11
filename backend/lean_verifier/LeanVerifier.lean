
import Mathlib.Tactic
import Mathlib.GroupTheory.Subgroup.Basic

theorem uniqueness_of_identity_element {G : Type*} [Group G] :
  ∀ (e f : G), (∀ a, e * a = a) → (∀ a, f * a = a) → e = f :=
begin
  intros e f he hf,
    apply he with a := f,
  -- STUDENT TACTICS WILL BE INSERTED HERE
end
