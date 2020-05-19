import permutation_representation.action_representation
import Tools.tools
import basic_definitions.matrix_representation
open is_basis linear_map character
universes u v  w w'

open general classical_basis
open finite_action
open fintype
variables (G : Type u) [group G]
          (R : Type v) [comm_ring R]
          (X : Type w)[fintype X][decidable_eq X]
          [mul_action G X]   


@[simp]theorem valvl  (g : G) : mat (Perm G R X) g  = λ x y,  if   g • y = x  then 1 else 0 := 
begin 
    apply matrix.ext,intros i j, 
    unfold mat,  unfold to_matrix,unfold to_matrixₗ, dsimp, --- faire mieux
    erw ← finite_action.Perm_ext, 
    erw action_on_basis_apply, 
end

lemma Grall (g : G) : (λ i : X, mat (Perm G R X) g i i) = (λ i : X, if  g • i = i then  1 else 0 ) := begin 
    funext,rw valvl,
end

@[simp]theorem χ_value_eq_fixed_point (g : G ): χ (Perm G R X) g = card ({x : X | g • x = x}  : set X):= 
begin 
    unfold χ,simp,exact rfl,
end
namespace Regular 

def Cayley_action (G : Type u) [group G] : mul_action G G := { 
    smul        := λ g r, g * r,
    one_smul    := begin intros, dsimp, rw one_mul, end,
    mul_smul    := begin  intros, dsimp, rw mul_assoc,end }

def Regular_representation (G : Type u) [group G][fintype G][decidable_eq G](R :Type v)[comm_ring R] : 
group_representation G R (G → R) := @Perm G R G _ _(Cayley_action G)

variables [fintype G][decidable_eq G]

lemma terere (X : Type u)[fintype X][decidable_eq X]  : (fintype.card ({x : X | true })) =  (fintype.card X)   := 
begin 
       exact fintype.card_congr (  equiv.set.univ X), 
end
/--
   `χ (Regular_representation G R ) g = if g = 1 then card G else 0  ` 
-/
theorem character_of_regular_representation (g : G):  χ (Regular_representation G R ) g = if g = 1 then card G else (0  ) := 
begin 
    erw χ_value_eq_fixed_point, 
    split_ifs,
    rw h,simp,apply congr_arg nat.cast, apply fintype.card_congr, 
    exact equiv.set.univ G,
    change _ = nat.cast 0,
    apply congr_arg nat.cast, simp,
    refine le_bot_iff.mp _,
    intro,
        intro hyp,
        simp at hyp, have r  : g * a = a,
            exact hyp,
        have rr : g = 1, 
            exact mul_left_eq_self.mp (congr_arg (has_mul.mul g) (congr_arg (has_mul.mul g) hyp)),
            trivial,
end
end Regular