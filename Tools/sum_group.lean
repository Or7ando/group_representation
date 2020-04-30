import .to_permutation
import .to_sum
open equiv

universe u 
/--
    For a group `G` and an element `g : G`,  `to equiv g` is the permutation (i.e `equiv G G`) define 
    by : `s ↦ s * g⁻¹` 
-/
def to_equiv {G : Type u}[group G](g : G) : perm G := { to_fun := λ s :G , s * g⁻¹ ,
  inv_fun := λ s : G , s * g,
  left_inv := begin 
   intros x,dsimp,
   rw mul_assoc, rw inv_mul_self,rw mul_one, end,
  right_inv :=  begin  intros x,dsimp,rw  mul_assoc, rw mul_inv_self, rw mul_one, end}

lemma to_equiv_ext {G : Type u}[group G](g : G) (s : G) : to_equiv g s = s * g⁻¹  := rfl
universe v 
/--
    Let `φ : G → X` with `fintype G` and `add_comm_monoid X`. 
    For `σ : perm X` we have : `∑ φ = ∑ φ ∘ σ`.   
-/
def Sum_equiv {G :Type u}{X : Type v}[fintype G](g : G)(φ :  G → X)[add_comm_monoid X] (σ : equiv.perm G) : 
            finset.sum finset.univ φ = finset.sum finset.univ (λ s, φ (σ s))
:= Sum_permutation φ  σ 

variables (G : Type)[group G](g : G)(X :Type) (φ : G → X)(hyp : fintype G)[add_comm_monoid X]
#check @Sum_equiv G X hyp g φ _ (to_equiv g) 
/-
theorem Per (f : M→ₗ[R]M') (g : G) : Σ (mixte_conj ρ π f) = Σ (λ s, mixte_conj ρ π f (s * g⁻¹)) := begin 
    sorry, 
end 
-/