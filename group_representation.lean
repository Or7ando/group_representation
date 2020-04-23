/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import linear_algebra.basic linear_algebra.finite_dimensional    
import algebra.module  
  
universe variables u v w w'  
   
open linear_map  

/- maybe needs a shorter name -/
/-- A representation of a group `G` on an `R`-module `M` is a group homomorphism from `G` to
  `GL(M)`. -/
def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M] [module R M] :
  Type* :=       G →* M ≃ₗ[R] M --- change ! 

variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'}
  [group G] [ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']
( ρ : group_representation G R M) 

instance  : has_coe_to_fun (group_representation G R M) := ⟨_, λ ρ , ρ.to_fun⟩

-- some test !   
lemma coersion ( ρ : group_representation G R M) : (ρ : G → M ≃ₗ[R] M)  = ρ.to_fun  := rfl
lemma coersion₂  ( ρ : group_representation G R M) (g : G) :    ρ  g = ρ.to_fun g
:= begin exact rfl,   end 

lemma coersion₂' (ρ : group_representation G R M) (g : G)  :
    (((ρ  g) : M ≃ₗ[R] M) : M →ₗ[R] M).to_fun = (ρ  g).to_fun  := rfl
lemma coersion₃ (ρ : group_representation G R M) (g : G) (x : M) : 
  (((ρ  g) : M ≃ₗ[R] M) : M →ₗ[R] M).to_fun x = (ρ  g).to_fun x := rfl
namespace group_representation  

/- do we want this instance? Then we don't have to write `(ρ g).1 x` instead of `ρ g x`. -/

lemma coersion₄ (ρ : group_representation G R M) (g : G) : 
 (((ρ  g) : M ≃ₗ[R] M) : M → M) = (((ρ g) : M ≃ₗ[R] M).to_fun  : M → M ):= rfl

lemma coersion₇ (ρ : group_representation G R M) (g : G) : 
    ((((ρ : G → (M ≃ₗ[R] M) )  g) : M →ₗ[R] M) : M → M) = (((ρ g) : M ≃ₗ[R] M)  : M → M ) :=  rfl

/-
    Juste quelques tests pour voir les commandes  function.comp_aplu
-/
variables  (x y : M)(g1 g2 : G) 

example :   ρ g1 ( x +  y) = ρ g1 x + ρ g1 y  :=  linear_map.map_add (ρ g1 : M →ₗ[R]M ) x y 

theorem rsmul ( r : R) :  (ρ g1)  (r • x) =  r • (ρ g1 x)  :=  linear_equiv.map_smul (ρ g1) r x  --- !!!!!! _root_.map_smul !!!!!!


example : ρ (g1 * g2)   = ρ g1 * ρ g2  := is_monoid_hom.map_mul ρ  g1 g2      

theorem rmap_one :  ((ρ 1) : M → M)  = id  := begin   rw ρ.map_one,
exact rfl, end
theorem refl ( g : G) : (((((( ρ : G →* (M ≃ₗ[R] M)) : (G →  M ≃ₗ[R] M)) g) : M ≃ₗ[R] M)  : M →ₗ[R] M) 
 : M → M) = (((ρ g) : M ≃ₗ[R] M)  : M → M ) := begin exact rfl, end
end group_representation