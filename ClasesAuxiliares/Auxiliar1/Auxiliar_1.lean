--                            |   Premisa  |
lemma Example_1 (A B : Prop) : A ∧ (A → B) → B :=
begin
    -- Complete
end
--                                |         Premisas          |
lemma Example_2 (A B C D : Prop) : (A ∨ B) → (A → C) → (B → D) → C ∨ D :=
begin
    -- Complete
end
--                            |  Premisa |
lemma Example_3 (A B : Prop) : ¬ (A ∧ B) → (A → ¬ B) :=
begin
    -- Complete
end