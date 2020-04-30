/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import linear_algebra.basic linear_algebra.finite_dimensional    
import algebra.module  
--infix  ` * `     := linear_map.comp 
universe variables u v w 
   
open linear_map  

/-- A representation of a group `G` on an `R`-module `M` is a group homomorphism from `G` to
  `GL(M)`. -/
def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M] [module R M] :
  Type* :=       G →* M ≃ₗ[R] M 

variables {G : Type u} [group G]
          {R : Type v} [ring R]
          {M : Type w}[add_comm_group M] [module R M] 

instance  : has_coe_to_fun (group_representation G R M) := ⟨_, λ ρ , ρ.to_fun⟩