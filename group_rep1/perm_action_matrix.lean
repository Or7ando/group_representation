import matrix_representation
import action_refondation
import matrix_representation_refondation 
set_option trace.simplify.rewrite true
open is_basis linear_map character 
--set_option trace.simplify true
universes u v  w w'
open general classical_basis
variables (G : Type u) [group G]
          (R : Type v) [comm_ring R]
          (X : Type w)[fintype X][decidable_eq X]
          [mul_action G X]   

open finite_action
open fintype
@[simp]theorem valvl  (g : G) : mat (Perm  R X) g  = λ x y,  if   g • y = x  then 1 else 0 := 
begin 
    apply matrix.ext,intros i j, 
    unfold mat,  unfold to_matrix,unfold to_matrixₗ, dsimp, --- faire mieux
    erw ← finite_action.Perm_ext, 
    erw action_on_basis_apply, 
end
lemma Grall (g : G) : (λ i : X, mat (Perm R X) g i i) = (λ i : X, if  g • i = i then  1 else 0 ) := begin 
    funext,rw valvl,
end
@[simp]theorem χ_value_eq_fixed_point (g : G ): χ (Perm R X) g = card ({x : X | g • x = x}  : set X):= 
begin 
    unfold χ,simp,exact rfl,
end
namespace Regular 
def Cayley_action (G : Type u) [group G] : mul_action G G := { smul := λ g r, g * r,
  one_smul := begin intros, dsimp, rw one_mul, end,
  mul_smul := begin  intros, dsimp, rw mul_assoc,end }
def Regular_representation (G : Type u) [group G][fintype G][decidable_eq G](R :Type v)[comm_ring R] : 
group_representation G R (G → R) := @Perm G R G _ _(Cayley_action G)
variables [fintype G][decidable_eq G]
#check Regular_representation G ℤ 
lemma terere (X : Type u)[fintype X][decidable_eq X]  : (fintype.card ({x : X | true })) =  (fintype.card X)   := begin 
    -- I don't understand why i'm always dealing with this kind of thing ???
       exact fintype.card_congr (  equiv.set.univ X), 
       
end
#check (Cayley_action G).smul
theorem hhh (g : G):  ((χ (Regular_representation G ℤ ) g) ) = if g = 1 then ( (card G)   ) else (0  ) := 
begin 
    erw χ_value_eq_fixed_point, 
    split_ifs,rw h,simp, apply fintype.card_congr, exact equiv.set.univ G,
    simp,refine le_bot_iff.mp _,intro,
        intro hyp,
        simp at hyp, have r  : g * a = a,
            exact hyp,
        have rr : g = 1, 
            exact mul_left_eq_self.mp (congr_arg (has_mul.mul g) (congr_arg (has_mul.mul g) hyp)),
            trivial,
end 
end Regular

