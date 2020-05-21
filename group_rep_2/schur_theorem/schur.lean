import tactic.push_neg
import basic_definitions.kernel_range  
import basic_definitions.equiv
import basic_definitions.sub_module
import Reynold_operator.reynold
open Kernel range morphism 
open stability open submodule linear_map
universe variables u v w w'


namespace morphism.from_irreductible 
open  linear_map
variables {G : Type u} [group G] {R : Type v}[ring R] 
variables {M1 : Type w}  [add_comm_group M1] [module R M1]
          {M2 : Type w'} [add_comm_group M2] [module R M2] 
          { ρ1 : group_representation G R M1}
          {ρ2 : group_representation G R M2}
          (f : ρ1 ⟶ᵣ ρ2)

/--
    let `f : ρ1 ⟶ᵣ ρ2` with `Irreductible ρ1` : `ker f is trivial`. 
-/
theorem ker_is_trivial  [Irreductible ρ1]  : (is_trivial (ker f.ℓ )) := Trivial ρ1 (ker f.ℓ)   

/-- 
    Let `f : ρ1 ⟶ᵣ ρ2` with `Irreductible ρ2` then `is_trivial range f` 
-/
theorem range_is_trivial [Irreductible ρ2]  :  is_trivial (range f.ℓ ) := Trivial ρ2 (range f.ℓ)

/--
     For  `f : ρ1 ⟶ᵣ ρ2`  with  `Irreductible ρ1` and `Irreductible ρ2` 
     if `(∃ x : M1, (f.ℓ  x ≠ 0))` then   `(ker f.ℓ  = ⊥ ) ∧  range f.ℓ  = ⊤` 
     so `f` is an `equivalence`
-/
theorem Schur₁ [Irreductible ρ1] [Irreductible ρ2] : (∃ x : M1, (f.ℓ  x ≠ 0)) →  
(ker f.ℓ  = ⊥ ) ∧  range f.ℓ  = ⊤ :=  
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


namespace shur₁_comm_ring
open  morphism.from_irreductible equiv_morphism


open_locale classical

variables {G : Type u} [group G] {R : Type v}[comm_ring R]{M : Type w}[add_comm_group M] [module R M]
variables  {ρ : group_representation G R M}  {M2 : Type w'} [add_comm_group M2] [module R M2]


variables  {ρ' : group_representation G R  M2}
theorem morphism_are_zero (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] : ∀ f : ρ ⟶ᵣ ρ', f = 0   
:= 
begin 
    by_contradiction,
    push_neg at a,rcases a with ⟨ φ, hyp ⟩,
    have : ∃ x, φ x ≠  0,
        simp, by_contradiction, push_neg at a, have : φ = 0, apply morphism.ext, 
        apply linear_map.ext, exact a, trivial,
    exact F (ker_im_equiv φ $ Schur₁ φ this),
end
open Reynold
variables [fintype G]

/--
    `F : not_isomorphic ρ ρ'  Irreductible ρ   Irreductible ρ'`
     The Reynold operator `Re ρ ρ'` is always zero. 
-/
theorem Reynold_is_zero (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ']:    Re ρ ρ' = 0 := 
begin 
    apply linear_map.ext,
    intros f,
    apply morphism_are_zero F,
end
end shur₁_comm_ring


namespace Schur₂
open  morphism.from_irreductible equiv_morphism


open_locale classical
variables {G : Type u} [group G] {R : Type v}[comm_ring R]{M : Type w}[add_comm_group M] [module R M]
variables  {ρ : group_representation G R M}
theorem Schur₂(f : ρ ⟶ᵣ ρ) [Irreductible ρ](r : R)(m0 : M) : 
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
open  morphism.from_irreductible

theorem Schur₂1(f : ρ ⟶ᵣ ρ) [Irreductible ρ](r : R)(m0 : M) : 
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