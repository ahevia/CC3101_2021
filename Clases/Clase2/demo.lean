/-
   lemma o theorem si se quiere dar un nombre al resultado, sino example
   Tipeo de → ∧ ∨ ¬ ↔ 
   Múltiples premisas
   Introducción del implica [intro(s)] y de la conjunción [apply and.intro]
-/ 
lemma Ejemplo1 (a b : Prop) : a → b → a ∧ b :=
begin
    intro ha, 
    intro hb,         -- can be replaced by [intros ha hb],
    apply and.intro,  -- can be replaced by [apply (and.intro ha hb)]
        apply ha,
        apply hb   
end


-- Eliminación de la conjunción [apply and.left, apply and.right]
lemma Ejemplo2 (a b : Prop) : a ∧ ¬b → ¬b ∧ a :=
begin
    intro h,
    apply and.intro,           -- can be replaced by [apply (and.intro (and.right h) (and.left h))]
        apply (and.right h),
        apply (and.left h)
end


-- Eliminación de la disyunción [apply or.elim]
lemma Ejemplo3 (a b c : Prop) : a ∨ b -> (a → c) -> (b → c) → c :=
begin
    intros hab hac hbc,
    apply (or.elim hab),   -- can be replaced by [apply (or.elim hab hac hbc)]
        apply hac,
        apply hbc
end


-- Eliminación del implica [apply premisa] e introducción de la disyunción [apply or.inl/inr]
lemma Ejemplo4 (a b c : Prop) : a -> (a ∨ b → c) → c :=
begin
    intros ha habc,
    apply habc,          -- can be replaced with [apply (habc (or.inl ha))]
        apply or.inl,
            apply ha
end


-- Introducción del iff [apply iff.intro]
lemma Ejemplo5 (a b : Prop) : a ∧ b ↔ b ∧ a :=
begin
    apply iff.intro,
        intro hab; apply (and.intro (and.right hab) (and.left hab)),
        intro hba; apply (and.intro (and.right hba) (and.left hba))        
end


-- Eliminación de la negación: ¬a se define como  a → false,
-- por lo que para eliminar ¬a debo eliminar el implica [aplicación]
-- Eliminación de false [false.elim]
lemma Ejemplo6 (a b : Prop) : a -> ¬a -> b :=
begin
    intros ha hna,
    apply false.elim,   -- can be replaced with [apply (false.elim (hna ha))]
    apply (hna ha)
end 


open classical
local attribute [instance] classical.prop_decidable

-- Logica clásica: prueba por reducción al absurdo.
-- Hay que agregar los dos comandos de arriba
-- Para probar una proposición, [by_contradiction] pide que
-- derivemos false a partir de la negación de la proposición. 
lemma Ejemplo7 (a : Prop) : ¬¬a → a :=
begin
    intro hnna,
    by_contradiction,
    apply (hnna a_1)
end


