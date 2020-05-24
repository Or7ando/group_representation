/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orlando Cau
-/
import linear_algebra.basic linear_algebra.finite_dimensional    
import algebra.module  
/-!
  We fix a notation composition of linear_map.
-/
notation f ` ⊚ `:80 g:80 :=  linear_map.comp f g

universe variables u v w 
   
open linear_map  

/-- A representation of a group `G` on an `R`-module `M` is a group homomorphism from `G` to
  `GL(M)`. 
  -/

def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M] [module R M] :
  Type* :=       G →* M →ₗ[R] M 

variables {G : Type u} [group G]
          {R : Type v} [ring R]
          {M : Type w}[add_comm_group M] [module R M] 

instance  : has_coe_to_fun (group_representation G R M) := ⟨_, λ ρ , ρ.to_fun⟩

variables (ρ : group_representation G R M)


@[simp]lemma map_comp (s t : G) : ρ (s * t) = ρ s ⊚ ρ t :=  ρ.map_mul _ _ 

def gr.to_equiv' (g : G) :  M ≃ₗ[R] M := { to_fun := ρ g,
  add := (ρ g).map_add ,
  smul := (ρ g).map_smul,
  inv_fun := (ρ g⁻¹ ),
  left_inv := begin intro, change (ρ g⁻¹ ⊚ ρ g) x = _, erw ←  map_comp, rw inv_mul_self, erw ρ.map_one, exact rfl end, 
  right_inv :=  begin intro, change (ρ g ⊚ ρ g⁻¹ ) x = _, erw ←  map_comp, rw mul_inv_self, erw ρ.map_one, exact rfl end, }

lemma gr.to_equiv : G →* M ≃ₗ[R] M := { to_fun := gr.to_equiv' ρ  ,
  map_one' := begin
      unfold gr.to_equiv', congr,erw ρ.map_one, exact rfl, rw one_inv, rw ρ.map_one,  exact rfl,
   end,
  map_mul' := begin
    intros, unfold gr.to_equiv', congr, rw map_comp, exact rfl,
    rw mul_inv_rev, rw map_comp, exact rfl,
   end } 

@[simp] lemma rho_symm_apply (x : M)(g : G) : ρ g ((gr.to_equiv ρ g).inv_fun x) = x := begin 
  dunfold gr.to_equiv, change (ρ g ⊚ ρ g⁻¹) x = x, rw ← map_comp, rw mul_inv_self, rw ρ.map_one, exact rfl,
end

@[simp] lemma symm_eq_inv (ρ : group_representation G R M) (g : G) : ρ g⁻¹ = (gr.to_equiv ρ g).symm :=
begin 
  ext, conv_lhs{
    erw ← rho_symm_apply ρ x g,
  },
  change (ρ g⁻¹ * ρ g) _ = _,
  erw ← ρ.map_mul, rw inv_mul_self, rw ρ.map_one, exact rfl, 
end 
