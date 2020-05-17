/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import linear_algebra.basic linear_algebra.finite_dimensional    
import algebra.module  
notation f ` ⊚ `:80 g:80 :=  linear_map.comp f g
universe variables u v w 
   
open linear_map  
#check comp_assoc
/-- A representation of a group `G` on an `R`-module `M` is a group homomorphism from `G` to
  `GL(M)`. -/
def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M] [module R M] :
  Type* :=       G →* M →ₗ[R] M 

variables {G : Type u} [group G]
          {R : Type v} [ring R]
          {M : Type w}[add_comm_group M] [module R M] 

instance  : has_coe_to_fun (group_representation G R M) := ⟨_, λ ρ , ρ.to_fun⟩

variables (ρ : group_representation G R M)


@[simp]lemma map_comp (s t : G) : ρ (s * t) = ρ s ⊚ ρ t :=  ρ.map_mul _ _ 
/-!
@[simp] lemma rho_symm_apply (x : M)(g : G) : ρ g ((ρ g).symm x) = x := by simp

@[simp] lemma symm_eq_inv (ρ : group_representation G R M) (g : G) : ρ g⁻¹ = (ρ g).symm :=
begin 
  ext, conv_lhs{
    erw ← rho_symm_apply ρ x g,
  },
  change (ρ g⁻¹ * ρ g) _ = _,
  erw ← ρ.map_mul, rw inv_mul_self, rw ρ.map_one,  exact rfl,
end 
-/