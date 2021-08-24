/-
Consideraciones:
  - Este ejercicio se puede resolver usando unicamente las herramientas vistas en clase, como
    intro, apply y by_contradiction.
  - Recuerde apoyarse en Lean_Tactics, pdf disponible en el material de la clase 2, sumado a lo
    visto en auxiliar y los ejemplos presentados en la Demo de Lean, clase 2.
Mucho exito!
-/

lemma Proof_1 (A B : Prop) : A → ¬ (¬ A ∧ B) :=
begin
    -- Complete
end

lemma Proof_2 (A B : Prop) : (¬ A ∧ ¬ B) → ¬ (A ∨ B) :=
begin
    -- Complete
end

lemma Proof_3 (A B C : Prop) : A → (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
begin
    -- Complete
end