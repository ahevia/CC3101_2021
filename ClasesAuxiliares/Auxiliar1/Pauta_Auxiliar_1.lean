--                            |   Premisa  |
lemma Example_1 (A B : Prop) : A ∧ (A → B) → B :=
begin
    -- Declaramos nuestra premisa, correspondiente a A ∧ (A → B)
    -- Notemos que buscamos concluir B
    intro h,
    -- h contiene dos partes claves, su lado derecho tiene el camino para llegar a B
    -- Entonces lo tomamos.
    apply and.right h,
    -- Pero para concluir B, requerimos que A sea valido, mas el lado izquierdo de h nos permite aseverarlo.
    apply and.left h
    -- Ganamos :D
end
--                                |         Premisas          |
lemma Example_2 (A B C D : Prop) : (A ∨ B) → (A → C) → (B → D) → C ∨ D :=
begin
    -- Declaramos nuestras premisas
    intros h1 h2 h3,
    -- Notando que h2 y h3 son las implicancias que nos acercan a C y D, respectivamente, necesitamos hacer
    -- validas las proposiciones necesarias. Para ello, hacemos un analisis por caso en base a h1.
    apply or.elim h1,
        -- Declaramos temporalmente a A como hipotesis.
        intro ha,
            -- Partimos demostrando el lado izquierdo de la conclusion, C.
            apply or.inl,
            -- Como tenemos h2, (A → C), y ha, A, podemos utilizar la eliminacion del implica, lo que nos demuestra C.
            apply h2,
            apply ha,
            -- Y ganamos por el lado izquierdo :D
        -- Ahora declaramos B como una hipotesis temporal, recordemos que es el segundo caso. Noten que ahora buscamos
        -- demostrar el lado derecho de nuestra conclusion, D, cuyos pasos son analogos a lo que hicimos para demostrar C.
        intro hb,
            -- Ojo que aqui declaramos la introduccion del or por la derecha, es decir, generar la patita derecha que nos falta
            -- de la conclusion, D.
            apply or.inr,
            apply h3,
            apply hb
    -- Y ganamoooos c:
end
--                            |  Premisa |
lemma Example_3 (A B : Prop) : ¬ (A ∧ B) → (A → ¬ B) :=
begin
    -- Declaramos nuestra premisa
    intro h,
    -- Lo que haremos es introducir el implica, donde asumimos A temporalmente.
    intro ha,
    -- De esta forma, debemos demostrar ¬ B, pero recordemos que esto es equivalente a decir B → false. Entonces nuevamente
    -- introducimos el implica, asumiento temporalmente B.
    intro hb,
    -- Asi, lo que buscamos es demostrar false. Para ello utilizaremos h, que es analogo a decir (A ∧ B) → false.
    apply h,
    -- Pero para cerrar, ahora necesitamos demostrar que tenemos (A ∧ B). Mas, notemos que somos personas bknes y ya tenemos las
    -- piezas necesarias, ha y hb. De tal forma que introducimos el and.
    apply and.intro,
    -- Entregando A
    apply ha,
    -- Entregando B
    apply hb
    -- Y asi demostramos que tenemos (A ∧ B), GANAMOS :DDDD
end