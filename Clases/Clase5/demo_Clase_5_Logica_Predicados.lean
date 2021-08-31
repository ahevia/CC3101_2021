-- Dominio de discurso 
variable A : Type

lemma Example1 (P Q : A → Prop) : 
(∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
begin
    intros hpq hp,
    intro a,
    apply hpq,  -- lines below can be replaced by apply ((hpq a) (hp a))
    apply hp    
end



lemma Example2 (P Q : A → Prop) : 
(∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) :=
begin
    apply iff.intro,
        -- [-->]
        intro hpq,
        apply and.intro,
            intro x, apply and.left (hpq x),
            intro x, apply and.right (hpq x),
        -- [<--]
        intro hpq,
        intro x,
        apply and.intro,
            apply ((and.left hpq) x),
            apply ((and.right hpq) x)
end


lemma Example3 (P Q : A → Prop) : 
(∃ x, P x ∧ Q x) → (∃ x, P x) :=
begin
    intro hpq,
    apply (exists.elim hpq), intros a ha,
    apply exists.intro a,
    apply (and.left ha)
end