import tactic

-- Exercise 1

-- (a)
variables p q : Prop
variable given1 : (p ∧ q)
example : p :=
show p, from and.left given1

-- (b)
--example : (p ∧ q → p) :=
--assume h1 : (p ∧ q),
--show p, from and.left h1

-- (c)
example : p → (q → p) :=
begin
  assume h1,
  assume h2,
  exact h1, 
end

-- (d)
example: p → (q → p ∧ q) :=  
begin
  assume h1,
  assume h2,
  split,
  exact h1,
  exact h2,
end
-- (f)
variable r : Prop
example : (p → (q → r)) → ((p → q) → (p → r)) :=
begin
  assume h1: p → (q → r),
  assume h2: p → q,
  assume h3: p,
  apply h1,
  exact h3,
  apply h2,
  exact h3,

end
-- (e)
example : (p → (q → r)) → (p ∧ q → r) :=
begin
  assume h1,
  assume h2: p ∧ q,
  cases h2 with h3 h4,
  apply h1,
  exact h3,
  exact h4,
  
end

-- (g)
example : ((p ∧ q) → r) → (p → (q → r)) :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h1,
  split,
  exact h2,
  exact h3,

end

-- (h)
example : (p ∧ q) → (p ∨ q) :=
begin
  intro h1,
  cases h1 with h2 h3,
  left,
  exact h2,

end

-- (i)
example : p → (q → p) :=
begin
  intro h1,
  intro h2,
  exact h1,

end

-- (j)
example : p ∧ (q ∨ (p → q)) → p ∧ q := 
begin
  intro h1,
  cases h1 with h2 h3,
  split,
  exact h2,
  cases h3 with h4 h5,
  exact h4,
  apply h5,
  exact h2,

end

-- 2. 
-- (a)
example : p ∧ (p → q) → p ∧ q :=
begin
  intro h1,
  cases h1 with h1 h2,
  split,
  exact h1,
  apply h2,
  exact h1,

end


-- (b)
example : (q → r) → ((p → q) → (p → r)) :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h1,
  apply h2,
  exact h3,

end

-- (c)
example : (p ∧ (q ∨ r)) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h1,
  cases h1 with h1 h2,
  cases h2 with h2 h3,
  left,
  split,
  exact h1,
  exact h2,
  right,
  split,
  exact h1,
  exact h3,

end

-- (d)
example : (¬ p ∧ (p ∨ q)) → q := 
begin
  intro h1,
  cases h1 with h1 h2,
  cases h2 with h2 h3,
  exfalso,
  show false, from h1 h2,
  exact h3,

end

-- (f)
example : (¬ (p ∨ q)) → (¬ p ∧ ¬ q) :=
begin
  intro h1,
  split,
  push_neg at h1,
  show ¬ p, from and.left h1,
  push_neg at h1, 
  show ¬ q, from and.right h1,

end

axiom lawOfExcludedMiddle :  p ∨ ¬ p → true
axiom pAndNotPImpF :  q ∧ ¬ q -> false
-- (g)
example : (p → q) → (¬ q → ¬ p) := 
begin 
  intro h1,
  intro h2,
  assume (hp : p),
  have hq : q, from h1 hp,
  have hf : q ∧ ¬ q, from and.intro hq h2,
  show false, from pAndNotPImpF hf,
  
end

-- The following code defines useful tools that we defined in Nat. deduction.
example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq







