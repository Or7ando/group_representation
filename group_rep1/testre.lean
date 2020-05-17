example {a : Type u} {s t : list α} : length (s ++ t) = length s + length t :=
list.rec_on s
(
    -- length t = length [] + length t
    -- length [] = 0 by definition
    -- 0 + x = x by definition
    show length ([] ++ t) = length [] + length t, from
    begin
        have z : [] ++ t = t, from rfl,
        rw z,
        have g : length [] = 0, from rfl,
        assumption,
        rw g,
        rw zero_add,
    end
)
(
    λ x y z,
    -- z : length (y ++ t) = length y + length t
    show length (x :: y ++ t) = length (x :: y) + length t, from
    begin
        show length (x :: y ++ t) = ((length y) + 1) + length t,
        have r : length (x :: y) = ((length y) + 1), refl,
        -- unfinished
    end
)
