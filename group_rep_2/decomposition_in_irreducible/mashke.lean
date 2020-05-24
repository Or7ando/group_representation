import Reynold_operator.reynold
import basic_definitions.kernel_range
import Tools.tools
open Reynold stability morphism_module linear_map
open_locale big_operators
universes  u v w w'
variables   {G : Type u} [group G][fintype G] 
            {R : Type v}[comm_ring R]  
            {M : Type w}[add_comm_group M] [module R M]  
            (ρ : group_representation G R M) 
            (W : submodule  R M)

theorem pre_mask (Hyp : has_projector W)  [stable_submodule ρ  W] (a : R )  (inv : a * (fintype.card G) = 1 ) : 
∃ F : ρ ⟶ᵣ ρ,is_projector F.ℓ ∧  linear_map.range (F.ℓ) = W   :=  
begin 
    rcases Hyp with ⟨p,hyp_p⟩,
    use a • (ℛ ρ ρ  p), 
    rw coe_smul,  
    erw reynold_ext,
    apply   sum_proj, assumption,
    apply conjugate_projector, exact  hyp_p.1,
    rw ←hyp_p.2 at *,
    apply @conj_mixte_range G _ _ R _ M _ _ ρ p _inst_6,
end 
namespace field
variables    
            {k : Type v}[comm_ring k]  
            {V : Type w}[add_comm_group V] [module R V]  
            (π  : group_representation G R V) 
            (F : submodule  R V)
            -- ici juste virer l'hypothèse has_projector ! 

end field 
