import .sub_module
import .morphism
import .kernel
open stability
universe variables u v w w'

lemma Fact {R : Type v}[ring R]{M1 : Type w}[add_comm_group M1] [module R M1] 
 (p1 : submodule R M1) (hyp : p1 = ⊤ ∨  p1 = ⊥ )(z : M1)(hyp' : z ∈ p1)(hyp'' : z ≠ 0) : p1 = ⊤   := begin 
    rcases hyp, assumption, rw hyp at hyp', rw submodule.mem_bot at hyp', by contradiction, 
end


variables {G : Type u} [group G] {R : Type v}[ring R] 

namespace Irreductible
variables  {M : Type w}[add_comm_group M] [module R M]  ( ρ : group_representation G R M) 


def Irreductible :=  ∀ {p : submodule R M},   (stable_submodule ρ p) → (p = ⊤ ∨  p = ⊥)

end Irreductible 

namespace morphism.from_irreductible 
open Irreductible
open Kernel range 
variables {M1 : Type w}  [add_comm_group M1] [module R M1]
          {M2 : Type w'} [add_comm_group M2] [module R M2] 
          { ρ1 : group_representation G R M1}
          {ρ2 : group_representation G R M2}
          (f : ρ1 ⟶ ρ2)

-- 
--  Faire les choses plus proprement en definissant une strucure ⊤ ⊥  sur les representation 
--
theorem pre_Schur_ker  (hyp : Irreductible ρ1) :  
(linear_map.ker (f.ℓ  : M1 →ₗ[R] M2) = ⊤  ∨ linear_map.ker (f.ℓ : M1 →ₗ[R] M2)  = ⊥  ) := 
 hyp  (ker_is_stable_submodule f)


theorem pre_Schur_range (hyp : Irreductible ρ2) :
 (linear_map.range (f.ℓ  : M1 →ₗ[R] M2) = ⊤  ∨ linear_map.range (f.ℓ  : M1 →ₗ[R] M2)  = ⊥  ) := 
 hyp (range_is_stable_submodule f)
/--
    little modification of Serre `Representations linéaires des groupes  finis`. 
    We have no assumption of field just a ring (`NOT` only commutative). `NOT` dimension. 
-/
theorem Schur₁  (hyp1 : Irreductible ρ1)(hyp2 : Irreductible ρ2) : (∃ x : M1, (f.ℓ  : M1 →ₗ[R] M2)  x ≠ 0) →  
(linear_map.ker (f.ℓ : M1 →ₗ[R] M2) = ⊥ ) ∧  linear_map.range (f.ℓ  : M1→ₗ[R] M2) = ⊤ := begin 
intros hyp_not_nul, rcases hyp_not_nul with ⟨x,hyp_not_nul⟩,
split, swap, apply Fact, 
    apply pre_Schur_range,assumption, 
    rw linear_map.mem_range,
    use x,
    exact hyp_not_nul,
    let schur :=  (hyp1 (ker_is_stable_submodule f)),unfold Ker at schur,
    rcases schur, swap,assumption,
    rw schur,
    have R :  x ∈ linear_map.ker (f.ℓ  : M1 →ₗ[R] M2),
            rw schur, trivial,
    rw linear_map.mem_ker at R,
    trivial,
end

#lint
end morphism.from_irreductible