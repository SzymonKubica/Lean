import tactic

variables (P Q R : Prop)

example : P → P :=
begin
    intro hP,
    exact hP,
end

example : P → (Q → P) :=
begin
    intro hP,
    intro hQ,
    exact hP,
end

example : P → Q → P :=
begin
    intro hP,
    intro hQ,
    exact hP,
end

theorem modus_ponens : P → (P → Q) → Q :=
begin 
    intro hP,
    intro hPQ,
    apply hPQ,
    exact hP,
end

theorem transitivity : (P → Q) → (Q → R) → (P → R) :=
begin 
    intro hPQ,
    intro hQR,
    intro hP,
    apply hQR,
    apply hPQ,
    exact hP,
end

example : (P → Q → R) → (P → Q) → (P → R) :=
begin 
    intro hPQR,
    intro hPQ,
    intro hP,
    apply hPQR,
    exact hP,
    apply hPQ,
    exact hP,
end

-- in Lean, the definition of ¬ P is 'P → false'
-- one can prove it by considerind what happens if the value of P is true or false
example : P → ¬ (¬ P) :=
begin 
    intro hP,
    change(¬ P → false),
    intro hnP,
    change P → false at hnP,
    apply hnP,
    exact hP,
end

example : P ∧ Q → P :=
begin 
    intro hPaQ,
    cases hPaQ with hP hQ,
    exact hP,
end

theorem and.elim' : P ∧ Q → (P → Q → R) → R :=
begin 
    intro hPaQ,
    intro hPQR,
    cases hPaQ with hP hQ,
    apply hPQR,
    exact hP,
    exact hQ,
end

theorem and.intro' : P → Q → P ∧ Q := 
begin 
    intro hP,
    intro hQ,
    split,
    exact hP,
    exact hQ,
end
