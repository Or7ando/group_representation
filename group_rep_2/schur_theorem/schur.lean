import tactic.push_neg
import basic_definitions.kernel_range
open Kernel range morphism 
open stability open submodule linear_map
universe variables u v w w'

namespace Irreductible
variables {G : Type u} [group G] {R : Type v}[ring R] 
variables  {M : Type w}[add_comm_group M] [module R M]   

def is_trivial (p : submodule R M) := (p = ⊤ ∨  p = ⊥)

class Irreductible ( ρ : group_representation G R M)  :=
 (certif: ∀ (p : submodule R M)[stable_submodule ρ p], is_trivial p)


def Trivial (ρ : group_representation G R M)(p : submodule R M) [Irreductible ρ] [stable_submodule ρ p]:= 
                Irreductible.certif ρ  p
end Irreductible 

namespace morphism.from_irreductible 
open Irreductible linear_map
variables {G : Type u} [group G] {R : Type v}[ring R] 
variables {M1 : Type w}  [add_comm_group M1] [module R M1]
          {M2 : Type w'} [add_comm_group M2] [module R M2] 
          { ρ1 : group_representation G R M1}
          {ρ2 : group_representation G R M2}
          (f : ρ1 ⟶ ρ2)

-- 
--  Faire les choses plus proprement en definissant une strucure ⊤ ⊥  sur les representation 
--


theorem ker_is_trivial  [Irreductible ρ1]  : (is_trivial (ker f.ℓ )) := Trivial ρ1 (ker f.ℓ)   

/--
    Let `f : ρ1 ⟶ ρ2` with `is_Irreductible ρ2` then `is_trivial range f` 
-/
theorem range_is_trivial [Irreductible ρ2]  :  is_trivial (range f.ℓ ) := Trivial ρ2 (range f.ℓ)


theorem Schur₁ [Irreductible ρ1] [Irreductible ρ2] : (∃ x : M1, (f.ℓ  x ≠ 0)) →  
(ker f.ℓ  = ⊥ ) ∧  range f.ℓ  = ⊤ :=  --- ici on peut penser a la notion d'equivalence ? 
begin
    intros hyp_not_nul,
    rcases hyp_not_nul with ⟨x,hyp_not_nul⟩,
    split,
    {
        rcases Trivial ρ1 (ker f.ℓ ),swap,assumption,
        have : f.ℓ  x = 0,
            rw ←  mem_ker, rw h, trivial,
        trivial,
        },
    {
        rcases Trivial ρ2 ( range f.ℓ ),
        assumption,
        have  : f.ℓ x ∈ range (f.ℓ ),
            rw mem_range, use x,
        rw h at this, rw  mem_bot at this, 
        trivial, 
        },
    
end
end morphism.from_irreductible

namespace Schur₂

open Irreductible morphism.from_irreductible


open_locale classical

variables {G : Type u} [group G] {R : Type v}[comm_ring R]{M : Type w}[add_comm_group M] [module R M]
variables  {ρ : group_representation G R M}
theorem Schur₂(f : ρ ⟶ ρ) [Irreductible ρ](r : R)(m0 : M) : 
         (m0 ≠ 0 ∧  f.ℓ m0 + r • m0 = 0) → (∀ m : M, f.ℓ m + r • m = 0) := 
begin 
    rintros ⟨spec,spectral⟩,
    let g :=  f + r • 𝟙 ρ,
    have  certif_contra :   m0 ∈ ker g.ℓ ,
        rw mem_ker,  exact spectral,
    by_contra,            
    push_neg at a,
    rcases a with ⟨ζ,hyp ⟩, change (g.ℓ ) ζ  ≠ 0 at hyp,
    let schur := (Schur₁ g) ⟨ζ, hyp⟩,
    rw [schur.1, mem_bot] at certif_contra, trivial, 
end
end Schur₂
namespace Sche 
variables {G : Type u} [group G] {R : Type v}[comm_ring R]{M : Type w}[add_comm_group M] [module R M]
variables  {ρ : group_representation G R M}
open Irreductible morphism.from_irreductible

theorem Schur₂1(f : ρ ⟶ ρ) [Irreductible ρ](r : R)(m0 : M) : 
         (m0 ≠ 0 ∧  f.ℓ m0 + r • m0 = 0) → (∃ m : M, f.ℓ m + r • m ≠  0) → 0  = 1 := 
begin 
    rintros ⟨spec,spectral⟩,
    rintros ⟨ζ ,hyp⟩,
    let g :=  f + r • 𝟙 ρ,
    have  certif_contra :   m0 ∈ ker g.ℓ ,
        rw mem_ker,  exact spectral,
    let schur := (Schur₁ g) ⟨ζ, hyp⟩,
    rw [schur.1, mem_bot] at  certif_contra, trivial,
    end
end Sche