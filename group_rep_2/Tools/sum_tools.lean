import data.fintype.basic
import linear_algebra.basic
open_locale big_operators
notation f ` ⊚ `:80 g:80  := linear_map.comp f g    
universes  u v w w' w''
open linear_map 
variables {G : Type u }[fintype G]
          {R : Type v}[comm_ring R] 
          {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M']
          {M'' : Type w''} [add_comm_group M''] [module R M'']
/-
    Here ` ⊚ ` denote the composition of linear application. We have a structure of `add_comm_monoid` 
    on ` M→ₗ[R]M' ` That ensure `∑ ` is well define.   
-/
/--
        `f ⊚  (∑ g, ρ g) = ∑ g, f ⊚ ρ g`
-/
lemma sum_left_comp (f : M' →ₗ[R]M'')(ρ : G → M →ₗ[R]M') :  f ⊚  (∑ g, ρ g) = ∑ g, f ⊚ ρ g  := 
begin 
    ext, rw linear_map.comp_apply,rw sum_apply,rw sum_apply, erw map_sum,
    exact rfl,
end
/--
    `(∑ t,  ρ t) ⊚  g = ∑  s, (ρ s) ⊚  g`
-/
lemma sum_right_comp (ρ : G → M →ₗ[R]M')(g : M'' →ₗ[R]M ) : (∑ t,  ρ t) ⊚  g = ∑  s, (ρ s) ⊚  g   := 
begin
    ext, rw linear_map.comp_apply,rw sum_apply,rw sum_apply, exact rfl,
end
example(ρ : G → M →ₗ[R]M')(x : M) :  (∑ g, ρ g ) x = ∑ g , (ρ g) x        := 
begin 
    rw sum_apply,
end
/--
    for a group `G` the map `g → g⁻¹` is a permutation of G.
-/
def inv_equiv {G : Type u}[group G] : equiv.perm G := {
  to_fun    := λ g, g⁻¹ ,
  inv_fun   := λ g, g⁻¹ ,
  left_inv  := inv_inv,
  right_inv := inv_inv,
}
lemma inv_equiv_ext      {G : Type u}[group G] (g : G) : inv_equiv.to_fun g = g⁻¹  := rfl
lemma inv_equiv_inv_ext  {G : Type u}[group G] (g : G) : inv_equiv.inv_fun g = g⁻¹ := rfl

variables {α : Type u} {β : Type v}
/--
    For a group `G` and an element `g : G`,  `to equiv g` is the permutation (i.e `equiv G G`) define 
    by : `s ↦ s * g⁻¹` 
-/
def to_equiv {G : Type u}[group G](g : G) : equiv.perm G := { 
    to_fun      := λ s :G , s * g⁻¹ ,
    inv_fun     := λ s : G , s * g,
    left_inv    := begin intros x,dsimp,rw mul_assoc, rw inv_mul_self,rw mul_one, end,
    right_inv   := begin  intros x,dsimp,rw  mul_assoc, rw mul_inv_self, rw mul_one, end
}
lemma finset.prod_univ_perm [fintype α] [comm_monoid β] {f : α → β} (σ : equiv.perm α) :
  ∏ x,  f x = ∏ x, f (σ x) :=
eq.symm $ finset.prod_bij (λ z _, σ z) (λ _ _, finset.mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _ H, σ.injective H) (λ b _, ⟨σ⁻¹ b, finset.mem_univ _, by simp⟩)  
/--
    For a permutation `σ : X → X` we have : `∑ x,  g x =  ∑ z, g (σ z) `
-/
lemma sum_univ_perm  {R :Type u}[add_comm_monoid R]{X : Type v}[fintype X](g : X → R)(σ : equiv.perm X )
: ∑ x,  g x =  ∑ z, g (σ z)  :=   @finset.prod_univ_perm _ (multiplicative R) _ _ g σ