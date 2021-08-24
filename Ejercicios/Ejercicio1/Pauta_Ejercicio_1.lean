open classical
local attribute [instance] classical.prop_decidable

lemma Proof_1 (A B : Prop) : A → ¬ (¬ A ∧ B) :=
begin
    intro ha,
    by_contradiction,
    apply and.left a,
    apply ha
end

-- Respuestas para Proof_2: Notar que siempre se puede hacer mas corto de lo que mostramos aqui.
-- Version granular
lemma Proof_2_1 (A B : Prop) : (¬ A ∧ ¬ B) → ¬ (A ∨ B) :=
begin
    intro h1,
    intro haob,
    apply or.elim haob,
        intro ha,
        apply (and.left h1),
        apply ha,
        intro hb,
        apply and.right h1,
        apply hb
end

-- Version compacta (viable)
lemma Proof_2_2 (A B C D : Prop) : (¬ A ∧ ¬ B) → ¬ (A ∨ B) :=
begin
    intro h1,
    by_contradiction h2,
    apply or.elim h2,
        intro ha,
        apply ((and.left h1) ha),
        intro hb,
        apply ((and.right h1) hb)
end

lemma Proof_3 (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
begin
    intro h,
    apply (or.elim (and.right h)),
        intro hb,
            apply or.inl,
            apply and.intro,
                apply (and.left h),
                apply hb,
        intro hc,
            apply or.inr,
            apply and.intro,
                apply (and.left h),
                apply hc
end