import matrix_representation
import action
import basis 
open is_basis linear_map character
--set_option trace.simplify true
universes u v  w w' 
variables (G : Type u) [group G]
          (R : Type v) [comm_ring R]
          (X : Type w)[fintype X][decidable_eq X]
          [mul_action G X]   
#check @χ G R _ _ X _ _
#check   (@Perm G R X _ _ _)
def χ_action := χ (@Perm G R X _ _ _)
#check χ_action G R X
/-!
    C'est très complexe. La manipulation des choses. 
-/
lemma  bis (x x_1 : X)(g : G) :  (λ (y : X), ite (x_1 = g • y) 1 0 * ε X R x y) = (λ y : X, ite (g⁻¹ • x_1 = y ) 1 0 * ε X R x y) := begin 
    funext,split_ifs,exact rfl, have t : g⁻¹ • x_1 = y, rw h, rw ←  mul_smul, rw inv_mul_self,
    rw one_smul, trivial,
    have r :  x_1 = g • y,
        rw ← h_1, rw ← mul_smul, rw mul_inv_self, rw one_smul, trivial, 
    rw zero_mul,
end

lemma encore : finset.sum finset.univ (λ y : X, 0) = 0  := begin 
    rw finset.sum_const_zero,
end
lemma ter (g : G)(x : X) : (@Perm G R X _ _ _) g   (ε  X R x)  =  ε X R (g • x) := 
begin 
    dunfold Perm,dsimp,rw rho_equiv_lin_ext, ext, rw rho_apply,
    unfold ε, split_ifs, exact rfl, 
    have r : g • x =  x_1, rw h, rw ← mul_smul, rw mul_inv_self, rw one_smul _, trivial,
    have r : x = g⁻¹ • x_1, rw ← h_1,rw ← mul_smul, rw inv_mul_self, rw one_smul _, trivial,
    exact rfl,
end
#check classical_basis X R 
lemma ter2 (x : X) :  
((λ (y : X), ite (x = y) 1 0 * ite (x = y) 1 0) : X → R) = (λ (y : X), ite (x = y) 1 0) := 
begin 
    funext, split_ifs, exact one_mul 1, exact zero_mul 0,
end
lemma ter3 {F G : X →   R} (H : F =G) : finset.sum finset.univ F = finset.sum finset.univ G :=begin
    exact congr_arg (finset.sum finset.univ) H,
end
/-- 
    Y'a une hypothèse ! ok
-/
lemma ter4 (g : G) (x x_1 : X) (hyp : ¬g • x = x_1) : 
    ((λ (y : X), ite (g⁻¹ • x_1 = y) 1 0 * ite (x = y) 1 0) : X → R )  = (λ y, 0) := begin 
    funext, split_ifs, rw ← h_1 at h, rw ← h at hyp, rw [← mul_smul, mul_inv_self, one_smul] at hyp,
     trivial,  exact mul_zero 1, exact zero_mul 1, exact zero_mul 0,
end
/--
Faire des petits lemmes pour que la démonstration soit le plus fluide
    possible 
-/


theorem valvl  (g : G) : mat (Perm  R X) g  = λ x y,  if x = g • y then 1 else 0 := 
begin 
    apply tools.proof_strategy, rw tools.mat_ext, rw to_matrix_to_lin,
    apply is_basis.ext (classical_basis X R),
    intro x,erw ter, rw matrix.to_lin_apply, 
    ext,
    rw matrix.mul_vec,
    erw bis,
    unfold ε, split_ifs,
    erw ←  h, rw ← mul_smul, rw inv_mul_self, rw one_smul, 
    let F :=  ter2 R X  x,
    let G := ter3 R X ,
    specialize G F, rw G,
    rw finset.sum_ite_eq, split_ifs,exact rfl, have r :x ∈ finset.univ,
    exact finset.mem_univ x, trivial,
    rw ter4,
    rw finset.sum_const_zero, exact h, use g,
    -- λ x : X,  
    -- finset.univ.sum (λy:n, M x y * v y),
    
end
lemma Grall (g : G) : (λ i : X, mat (Perm R X) g i i) = (λ i : X, if i = g • i then  1 else 0 ) := begin 
    funext,rw valvl,
end
theorem χ_value_eq_fixed_point (g : G ): χ_action G R X g = fintype.card {x : X | x = g • x } := 
begin 
    unfold χ_action, 
    unfold χ,
    dunfold matrix.trace,  -- la notation ∑  et faire une chose direc sur la trace
    dunfold matrix.diag, dsimp, -- Il nous faut mieux travailler  χ avoir une expression direct χ g := ∑ mat (ρ g) i i 
    rw Grall, 
    rw finset.sum_boole,simp, exact rfl,
end