
import Mathlib.Tactic
import Mathlib.GroupTheory.Subgroup.Basic

-- This is the formal statement of the theorem we are trying to prove.
theorem uniqueness_of_identity_element {G : Type*} [Group G] :
  ∀ (e f : G), is_identity e → is_identity f → e = f :=
begin
  -- Let e and f be two identity elements in the group G.
  intros e f he hf,
  -- Our goal is to prove that e = f.
  -- The proof state is now ready for your first step.

    have h₁ := (he f).left;
  have h₂ := (hf e).right,
  -- STUDENT TACTICS WILL BE INSERTED HERE

end
