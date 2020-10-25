import tactic

import data.real.basic

example: ∀ x : ℝ, ∃ y : ℝ, x + y > 0 :=
begin 
    intro x,
    use 64-x,
    simp,
    norm_num,
end

-- ∃ y : ℝ, ∀  x : ℝ, x + y > 0 :=
-- Is not true, as we can prove the opposite.

example: ¬ (∃ y : ℝ, ∀  x : ℝ, x + y > 0) :=
begin 
    push_neg,
    intro y,
    use -73 - y,
    simp,
    norm_num,
end

variable (α : Type)
-- P is a predicate of α so it is a function that assigns a true-false for each x : alpha.
example : (α → Prop) ≃ set α :=
{ to_fun := λ P, {x : α | P x},
  inv_fun := λ X, λ a, a ∈ X,
  left_inv:= begin 
      intro P,
      dsimp,
      refl,
  end
  ,
  right_inv  := begin
      intro P,
      dsimp,
      refl,
  end
}