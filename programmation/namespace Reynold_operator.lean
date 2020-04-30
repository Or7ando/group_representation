namespace Reynold_operator
namespace Group.tools
open equiv
def to_equiv {G : Type u}[group G](g : G) : perm G := { to_fun := λ s, g*s,
  inv_fun := λ s, g⁻¹ *s,
  left_inv := begin dsimp, intros x,rw ← mul_assoc, rw inv_mul_self, rw one_mul,  end,
  right_inv :=  begin dsimp, intros x,rw ← mul_assoc, rw mul_inv_self, rw one_mul, end}
end Group.tools
open morphism
variables {G : Type u} [group G] [fintype G]{R : Type v}[comm_ring R] {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M']
          {f : G → (M →ₗ[R] M)}
notation  `Sum` := finset.sum finset.univ 

constants (a: R)[hyp : a * ((fintype.card G) : R) = 1]


lemma Reynold_invariant (g : G) (h1 : G → M→ₗ[R]M') : Sum h1 =  Sum ( λ z, h1(Group.tools.to_equiv g z))  :=
 Sum_permutation h1 (Group.tools.to_equiv g)



def Reynold {G : Type u} [group G][fintype G](f : G → (M →ₗ[R] M'))  : M→ₗ[R]M' :=   Sum f

notation `ℳ `  := Reynold 
variables (h1 h2 : M→ₗ[R] M')
#check a • h1+h2
lemma Reynold.add (h1 h2 : G  → M→ₗ[R] M') : ℳ (h1 + h2) =  ℳ h1  + ℳ h2 := 
begin 

sorry, end
lemma Reynold.mul (a : R )(h1  : G  → M→ₗ[R] M') : ℳ ( a • h1 )= a •  ℳ h1   := 
begin    
sorry,
 end
def mul_left (g : G) (h1 : G → M→ₗ[R]M') : G → M→ₗ[R]M' := λ s, h1 (s* g)
open technical
lemma Reynold_permutation (g : G) (h1 : G → M→ₗ[R]M') : ℳ ( λ z, h1(Group.tools.to_equiv g z)) = ℳ h1 :=
 begin 
       unfold Reynold, erw ← Sum_permutation,  
end 
/--
    Let `ρ and π` two representation on `M` and `M'`. Let `f : M →ₗ[R] M'` a `linear_map`. 
    Let  `ℒ f := Σ_{g ∈ G} π g⁻¹ ∘ f ∘ ρ  g`,   then  `ℒ f` is a morphism `ρ ⟶ π`. 
    Proof :  `∀ t ∈ G,  ρ t ∘ ℒ f ∘ π t⁻¹  := ∑ ρ t g⁻¹  ∘ f ∘ π g t  = ∑  t'⁻¹  ∘  f ∘ π t'`    
-/
def ℒ (ρ : group_representation G R M) (ρ'  : group_representation G R M') (f : M→ₗ[R]M') := Sum (λ g : G, (ρ' g⁻¹ : M' →ₗ[R] M')  * f * (ρ g : M →ₗ[R]M )) 
#check @ℒ 
open equiv function fintype finset
theorem pre_morphism (ρ : group_representation G R M) (ρ'  : group_representation G R M') (f : M→ₗ[R]M') 
 (s : G) :  ρ' s  ∘   (ℒ  ρ ρ' f) 
  = ℒ ρ ρ' f  ∘  ρ s  := begin 
    ext, rw function.comp_apply,dunfold ℒ at ⊢,dsimp, sorry,
  end

#check ℳ 
end Reynold_operator

namespace TEST
variables {G : Type u} [group G][fintype G]  {R : Type v}[comm_ring R] {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M']
          (φ : G → (M →ₗ[R]M'))
          (f : M' →ₗ[R]M') 
lemma hello  :  f *  (finset.sum finset.univ φ) = finset.sum finset.univ (λ g, f * (φ g)) := begin 
    ext,simp, 
end   