import group_representation 
import morphism
import Tools.to_sum  
import Tools.sum_group
/-!
*    Let `ρ and π` two representations on `M` and `M'`. Let `f : M →ₗ[R] M'` a `linear_map`. 
*    Let  `ℒ f := Σ_{g ∈ G} π g⁻¹ ∘ f ∘ ρ  g`,   then  `ℒ f` is a morphism `ρ ⟶ π`. 
*    Proof :  `∀ t ∈ G,  ρ t ∘ ℒ f ∘ π t⁻¹  := ∑ ρ t g⁻¹  ∘ f ∘ π g t  = ∑  t'⁻¹  ∘  f ∘ π t'`    

#    We start to define sum operator on `M →ₗ[R] M'`  
*     Let `(X : Type u)[fintype X]` and ` φ : X → M→ₗ[R]M'`. We fix a notation for 
*    `finset.sum finset.univ φ := Σ φ`.  
-/
universes  u v w w'
open linear_map TEST
/-!
*   We illustrate in a first time the name of the function.
-/
namespace Illustration
notation `Σ` := finset.sum (finset.univ)
variables {G : Type u } [group G][fintype G]
          {R : Type v}[comm_ring R] 
          {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M']
          (ρ : G → M →ₗ[R]M')
          (f : M' →ₗ[R]M') 
          (g : M →ₗ[R]M) 
          (x : M)
/-!
    Here ` * ` denote the composition of linear application. We have a structure of `add_comm_monoid` 
    on ` M→ₗ[R]M' ` That ensure `Σ` is well define.  
-/
example :  f * Σ ρ  = Σ  (λ s, f * ρ s)     := Sum_comp_left ρ f 
example :  (Σ ρ) * g = Σ (λ s, (ρ s) * g )  := Sum_comp_right ρ g 
example :  (Σ ρ ) x = Σ (λ g, ρ g x)        := Sum_apply ρ x 

end Illustration

variables {G : Type u} [group G][fintype G]
          {R : Type v}[comm_ring R]   --- Commutative ring  

namespace Reynold
open Illustration
variables {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'] 
          (ρ : group_representation G R M)
          (π : group_representation G R M')

lemma coersion (s g : G) : (((ρ s * ρ g⁻¹) * ρ g) : M→ₗ[R]M) = linear_map.comp ((ρ s * ρ g⁻¹) : M→ₗ[R] M )  (ρ g : M→ₗ[R]M )  := rfl
/--
    We start to define `mixte_conj (f : M→ₗ[R]M')(s : G) : M→ₗ[R] M' := π s⁻¹ * f * ρ s`
-/
def mixte_conj (f : M→ₗ[R]M') : G →   M→ₗ[R] M' := λ s, ↑(π s⁻¹)  * f * ↑(ρ s) 

lemma mixte_conj_ext (f : M→ₗ[R]M')(s : G) : mixte_conj ρ π f s = ↑(π s⁻¹)  * f * ↑(ρ s) := rfl
/--
        we have `∀ g : G, (π g) (π s⁻¹) * f * ρ s = π (s g⁻¹)⁻¹  * f * ρ (s g⁻¹) * ρ g` 
        so `π  g * mixte_conj s = mixte_conj (s g⁻¹) ρ g`
-/
theorem mixte_conj_mul_left (f : M→ₗ[R]M') (g : G)(s : G):
 ↑(π g) * (mixte_conj ρ π f s) = (mixte_conj ρ π f (s * g⁻¹)) * ↑(ρ g ) :=
 begin 
    rw mixte_conj_ext, rw mixte_conj_ext,
    erw mul_inv_rev, rw inv_inv, rw π.map_mul, rw ρ.map_mul,
    erw linear_map.comp_assoc ↑(ρ g),  rw ← coersion ρ s g,
    rw mul_assoc, rw ← ρ.map_mul , rw inv_mul_self, rw ρ.map_one, rw mul_one, exact rfl, 
 end
theorem mixte_conj_mul_left_fun (f : M→ₗ[R]M') (g : G) : 
        (λ s : G, ↑(π g) * (mixte_conj ρ π f s)) = (λ s, (mixte_conj ρ π f (s * g⁻¹)) * ↑(ρ g )) :=
begin 
    ext,rw mixte_conj_mul_left,
end
/--
    The operator `ℒ`  
-/
def ℒ (f : M→ₗ[R]M') : M→ₗ[R] M' := finset.sum finset.univ (mixte_conj ρ π f)
/--
*   
* 
-/
theorem Per (f : M→ₗ[R]M') (g : G) : Σ (mixte_conj ρ π f) = Σ (λ s, mixte_conj ρ π f (s * g⁻¹)) := 
     @Sum_equiv G (M→ₗ[R]M') _ g (mixte_conj ρ π f) _ (to_equiv g)


theorem L_is_morphism (f : M→ₗ[R]M') (g : G) : (π g : M'→ₗ[R]M') * (ℒ ρ π  f) = (ℒ ρ π  f) * (ρ g : M→ₗ[R] M) :=  begin 
    unfold ℒ,
    erw Sum_comp_left,
    rw  mixte_conj_mul_left_fun, 
    rw ← Sum_comp_right, 
    rw Per ρ π  f g,
end
/--
    The Reynold opérator.  
-/
def ℛ : (M→ₗ[R]M') → (ρ ⟶  π) := λ f, { ℓ := ℒ ρ π f,
  commute := begin
        intros g, ext x, rw function.comp_apply, 
        let theo := L_is_morphism ρ π f g,
        rw linear_map.ext_iff  at theo,
        specialize theo x,
        rw linear_map.comp_apply at theo,
        erw ← theo, exact rfl, 
   end }
lemma reynold_ext(f : M →ₗ[R]M' ) : (ℛ ρ π f).ℓ = finset.sum finset.univ (mixte_conj ρ π f) := rfl  
#check ℛ ρ
end Reynold
namespace more_on_mixte_conj
open Reynold 
end more_on_mixte_conj