import basic_definitions.group_representation
import basic_definitions.morphism
import tactic.apply_fun
import basic_definitions.sub_module
import Tools.tools
set_option pp.generalized_field_notation false
open_locale big_operators    ----  his there a standart notation ? 
/-!
*    Let `ρ and π` two representations on `M` and `M'`. Let `f : M →ₗ[R] M'` a `linear_map`. 
*    Let  `ℒ f := Σ_{g ∈ G} π g⁻¹ ∘ f ∘ ρ  g`,   then  `ℒ f` is a morphism `ρ ⟶ᵣ π`. 
*    Proof :  `∀ t ∈ G,  ρ t ∘ ℒ f ∘ π t⁻¹  := ∑ ρ t g⁻¹  ∘ f ∘ π g t  = ∑  t'⁻¹  ∘  f ∘ π t'`    

#    We start to define sum operator on `M →ₗ[R] M'`  
*     Let `(X : Type u)[fintype X]` and ` φ : X → M→ₗ[R]M'`. We fix a notation for 
*    `finset.sum finset.univ φ := Σ φ`.  The notation change in mathlib taht cool 
-/
universes  u v w w' w''
open linear_map 
/-!
*   We illustrate in a first time the name of the function.
-/
namespace Illustration
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
    I don't know if this lemma is on mathlib so i rename it in a file tools. 
-/
example :  f ⊚  (∑ g, ρ g) = ∑ g, f ⊚  (ρ g)  := 
begin 
    erw sum_left_comp,
end

example : (∑ t,  ρ t) ⊚  g = ∑  s, (ρ s) ⊚  g   := 
begin
    erw sum_right_comp,
end
example :  (∑ g, ρ g ) x = ∑ g , (ρ g) x        := 
begin 
    rw sum_apply,
end

end Illustration

variables {G : Type u} [group G][fintype G]
          {R : Type v}[comm_ring R]   --- Commutative ring  

namespace Reynold
open Illustration
variables {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'] 
          (ρ : group_representation G R M)
          (π : group_representation G R M')

/--
    `mixte_conj π ρ f s  : M→ₗ[R] M' := π s⁻¹ * f * ρ s`
-/
def mixte_conj (f : M→ₗ[R]M') : G →   M→ₗ[R] M' := λ s, π s⁻¹  ⊚  f ⊚  ρ s

lemma mixte_conj_ext (f : M→ₗ[R]M')(s : G) : mixte_conj ρ π f s = (π s⁻¹)  ⊚   f ⊚  (ρ s) := rfl
/--
        we have `∀ g : G, (π g) (π s⁻¹) * f * ρ s = π (s g⁻¹)⁻¹  * f * ρ (s g⁻¹) * ρ g` 
        so `π  g * mixte_conj s = mixte_conj (s g⁻¹) ρ g`
-/
theorem mixte_conj_mul_left (f : M→ₗ[R]M') (g : G)(s : G):
 (π g) ⊚  (mixte_conj ρ π f s) = (mixte_conj ρ π f (s * g⁻¹)) ⊚  (ρ g ) :=
 begin 
    rw mixte_conj_ext, rw mixte_conj_ext, 
    erw mul_inv_rev, rw inv_inv, rw map_comp,
    conv_rhs {
        rw  comp_assoc (ρ g),
        rw ← map_comp ρ , rw mul_assoc, rw inv_mul_self, rw mul_one,
    },
    ext, exact rfl,
end

/--
    The operator `ℒ`  
-/
def ℒ (f : M→ₗ[R]M') : M→ₗ[R] M' := ∑ s, mixte_conj ρ π f s

/--
    Ici j'ai détaillé la preuve 
-/
theorem Per (f : M→ₗ[R]M') (g : G) : ∑ s, mixte_conj ρ π f s   = ∑  s, mixte_conj ρ π f (s * g⁻¹) := 
sum_univ_perm (mixte_conj ρ π f) (to_equiv g)
    
open morphism

theorem L_is_morphism (f : M→ₗ[R]M')  :  is_invariant ρ π (ℒ ρ π f)    :=  
begin 
    unfold ℒ,  intros g,
    erw sum_left_comp,
    rw Per ρ π  f g,
    erw  sum_right_comp,
    congr,funext s, 
    rw mixte_conj_mul_left,
end
/--
    The Reynold opérator.  
-/

def ℛ : (M→ₗ[R]M') → (ρ ⟶ᵣ  π) := λ f, to_morphism (ℒ ρ π f) (L_is_morphism ρ π f )

lemma reynold_ext(f : M →ₗ[R]M' ) : (ℛ ρ π f).ℓ = ∑ s, mixte_conj ρ π f s := rfl  
#check ℛ ρ ρ 
/-!
    THE Reynold opérator is linear ! 
        note the structure of module of ρ ⟶ᵣ ρ' is define in the file 
        `basic_definition.morphism_module`

    Remarque je n'ai toujours pas inversé le cardinal de G pour des raisons de confort ! 
-/
variables {M'' : Type w''} [add_comm_group M''] [module R M'']
lemma comp_left_distrib (a : M' →ₗ[R]M'')(b c : M →ₗ[R]M') : a ⊚ (b + c) = a ⊚ b + a ⊚ c :=
begin 
    intros, ext x, erw map_add, exact rfl,
end
lemma comp_smul (r : R) (a : M' →ₗ[R]M'')(b  : M →ₗ[R]M') : a ⊚  (r • b) = r • (a ⊚ b) := 
begin 
    intros,ext,erw map_smul, exact rfl,
end
def Re : (M→ₗ[R]M') →ₗ[R] (ρ ⟶ᵣ  π) := { 
    to_fun := ℛ ρ π ,
    add := 
    begin
        intros f1 f2, apply morphism.ext,
        rw morphism_module.add_coe,  
        erw ← multiset.sum_map_add,rw reynold_ext, congr, funext,
        rw mixte_conj_ext, erw comp_left_distrib, exact rfl,
  end,
  smul := begin  -- mieux avec morphism.ext
    intros r f,apply morphism.ext, rw morphism_module.coe_smul,
    rw reynold_ext, rw reynold_ext,rw finset.smul_sum, congr,
    funext,
    rw mixte_conj_ext,
    rw comp_smul,
    exact rfl,
  end }
lemma reynold_ext'(f : M →ₗ[R]M' ) : (Re ρ π f).ℓ  = ∑ s, mixte_conj ρ π f s  := rfl 
end Reynold
open Reynold 
variables {M : Type w}  [add_comm_group M] [module R M] (ρ : group_representation G R M)

lemma comp_conjugate (p1 p2  : M→ₗ[R]M ) (g : G) :  (mixte_conj ρ ρ (p1 ) g)  * mixte_conj ρ ρ p2 g =  mixte_conj ρ ρ (p1 * p2) g := 
begin 
    rw mixte_conj_ext,
    change _ ⊚ ( p1 ⊚ (ρ g ⊚  ρ  g ⁻¹) ⊚  p2 ) ⊚  _ = _,
    rw ← map_comp, rw mul_inv_self, rw ρ.map_one, erw comp_id, exact rfl,
end 
/--
    `is_projector p ` →  `is_projector (mixte_conj ρ ρ p g)`
-/
lemma conjugate_projector (p : M→ₗ[R]M )(hyp : is_projector p) (g : G) : is_projector (mixte_conj ρ ρ p g) :=
begin 
    unfold is_projector at *,
    rw comp_conjugate, rw hyp,
end 
/--
    `range (p * ρ g) =   (range p )`
-/
lemma pre_compose_range (p : M→ₗ[R]M ) (g : G) : range (p * ρ g) =   (range p ) := 
begin 
        apply le_antisymm, 
        {unfold range, erw  submodule.map_comp, apply submodule.map_mono, exact le_top},
        rw submodule.le_def', intros x,  intros hyp, rcases hyp with ⟨z,hyp_z ⟩,  use (ρ g⁻¹ ) z, split, 
        change (ρ g⁻¹ ) z ∈ ⊤ ,
        trivial, rw ←  hyp_z.2,
        change  p  (( ρ g ⊚ ρ g⁻¹ ) z ) = p z,
        rw ← map_comp, rw mul_inv_self, rw ρ.map_one, exact rfl,
end
lemma conjugate_range (p : M→ₗ[R]M ) (g : G) : range (mixte_conj ρ ρ p g) = submodule.map (ρ g⁻¹ )  (range p ) := 
begin 
    unfold mixte_conj,
    erw ← submodule.map_comp, erw pre_compose_range, 
    exact rfl,
end
open stability
lemma conj_mixte_range (p : M→ₗ[R]M )[stable_submodule ρ (range p)] (g : G)  : range (mixte_conj ρ ρ p g) = range p :=
begin 
    rw conjugate_range,
    rw stability.map,
end
