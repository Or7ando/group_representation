import tactic
import .sub_module
import tactic.push_neg
import .morphism
import .homothetic
import .kernel
open Kernel range morphism homothetic
open stability
universe variables u v w w'

lemma Fact {R : Type v}[ring R]{M1 : Type w}[add_comm_group M1] [module R M1] 
 (p1 : submodule R M1) (hyp : p1 = ⊤ ∨  p1 = ⊥ )(z : M1)(hyp' : z ∈ p1)(hyp'' : z ≠ 0) : p1 = ⊤   := begin 
    rcases hyp, assumption, rw hyp at hyp', rw submodule.mem_bot at hyp', by contradiction, 
end

namespace Irreductible
variables {G : Type u} [group G] {R : Type v}[ring R] 
variables  {M : Type w}[add_comm_group M] [module R M]  ( ρ : group_representation G R M) 
def Irreductible :=  ∀ {p : submodule R M},   (stable_submodule ρ p) → (p = ⊤ ∨  p = ⊥)

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
theorem pre_Schur_ker  (hyp : Irreductible ρ1) :  
(ker f.ℓ  = ⊤  ∨ ker f.ℓ   = ⊥  ) :=   hyp  (ker_is_stable_submodule f)


theorem pre_Schur_range (hyp : Irreductible ρ2) :
 (range f.ℓ  = ⊤  ∨ range f.ℓ   = ⊥  ) := 
 hyp (range_is_stable_submodule f)
 open linear_map
variables (hyp : Irreductible ρ2 )
#check f
#check  pre_Schur_range f (by assumption) 
/--
    little modification of Serre `Representations linéaires des groupes  finis`. 
    We have no assumption of field just a ring (`NOT` only commutative). `NOT` dimension. 
-/





theorem Schur₁  (hyp1 : Irreductible ρ1)(hyp2 : Irreductible ρ2) : (∃ x : M1, (f.ℓ  x ≠ 0)) →  
(ker f.ℓ  = ⊥ ) ∧  range f.ℓ  = ⊤ := 
begin
    intros hyp_not_nul,
    rcases hyp_not_nul with ⟨x,hyp_not_nul⟩,
    split, swap, 
    apply Fact, -- ici ?  
    apply pre_Schur_range, --- on ne comprend plus !
    assumption, 
    rw linear_map.mem_range,
    use x,
    exact hyp_not_nul,
    let schur :=  (hyp1 (ker_is_stable_submodule f)),unfold Ker at schur,
    rcases schur, swap,assumption,
    rw schur,
    have R :  x ∈ ker f.ℓ ,
            rw schur, trivial,
    rw linear_map.mem_ker at R,
    trivial,
end
end morphism.from_irreductible
namespace Schur₂
open Irreductible morphism.from_irreductible
open_locale classical
variables {G : Type u} [group G] {R : Type v}[comm_ring R]{M : Type w}[add_comm_group M] [module R M]
variables  {ρ : group_representation G R M}
theorem Schur₂(f : ρ ⟶ ρ) [re : Irreductible ρ] : (∃ r : R, ∃ m0 : M, m0 ≠ 0 ∧  f.ℓ m0 + r • m0 = 0) → (∃ r : R, ∀ m : M, f.ℓ m + r • m = 0) := begin 
    intro hyp,
    rcases hyp with ⟨r,m0,⟨spec,spectral⟩⟩,
    use r,
    let g :=  f + r • 𝟙 ρ,
    have  certif_m0_in_ker : g.ℓ  m0 = 0,
        erw [add_ext,
         smul_ext, one_ext],
        exact spectral,
    let schur := (Schur₁ g) ( by assumption  ) (by assumption), -- swap, exact re   
    by_contra,                  -- re doesnt work 
    push_neg at a,
    rcases a with ⟨ζ,n ⟩, 
    have R : (f.ℓ) ζ + r • ζ = g.ℓ ζ, 
        erw  [add_ext,smul_ext,one_ext],
        exact rfl, 
    rw R at n, 
    let V := (schur ⟨ζ,n⟩).1,
    have : m0 ∈ linear_map.ker g.ℓ,
        rw linear_map.mem_ker,
        exact certif_m0_in_ker,
    rw V at this,
    rw submodule.mem_bot at this,
    by contradiction,
end
/-
example (P : Prop) (h : P ∨ ¬ P) : ¬ ¬ P → P := begin 
    intros hnn,
    cases h,
    assumption,
    by contradiction,
end
example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := begin 
        split,
        intro hpq,
        intro hnQ,
        intro hp,
        end

example (X :Type) (P : X → Prop ) (hyp : (∃ x : X, ¬ (P x)) → false ) : ∀ x, P x := begin
    intro,
    contrapose! hyp,
    use x,
end

example (X :Type) (P : X → Prop ) (hyp : (∃ x : X, ¬ (P x)) → false ) : ∀ x, P x := begin
  by_contra,
  rw not_forall at a,
  exact hyp a,
end
-/