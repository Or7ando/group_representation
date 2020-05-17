import .group_representation 
universe variables u v w w' w'' w'''

open linear_map

variables {G : Type u} [group G] {R : Type v}[ring R] 
 
namespace morphism
variables {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'] 


/--
  a morphism `f : ρ ⟶ π` between representation is a linear map `f.ℓ : M(ρ) →ₗ[R] M(π)` satisfying 
    `f.ℓ ∘   ρ g  = π g  ∘   f.ℓ` has function on `set`. 
-/
structure morphism  (ρ : group_representation G R M) (π : group_representation G R M') : Type (max w w') := 
  (ℓ : M →ₗ[R] M')
  (commute : ∀(g : G), ℓ ∘   ρ g  = π g  ∘   ℓ) --- en terme d'élément ! 

variables (ρ : group_representation G R M)

infixr ` ⟶ `:25 := morphism 


@[ext]lemma ext  {ρ : group_representation G R M} {ρ'  : group_representation G R M'} ( f g : ρ ⟶ ρ') : 
(f.ℓ)  = g.ℓ  → f = g := 
begin 
    intros, 
    cases f,cases g , congr'; try {assumption},
end

variables  (ρ'  : group_representation G R M') 

instance : has_coe_to_fun (morphism ρ ρ') := ⟨_,λ f, f.ℓ.to_fun⟩  

lemma coersion (f : ρ ⟶ ρ') : ⇑f = (f.ℓ) := rfl

theorem commute_apply ( f : ρ ⟶  ρ') (x : M) (g : G) : f ( ρ g x) = ρ' g (f x ) := begin 
      change (f.ℓ  ∘ ρ g ) x = _,
      rw f.commute, exact rfl,
  end
theorem 𝒞_o_e_r_s_i_o_n__s__ℓ( f : ρ ⟶  ρ')(g : G) : f.ℓ ∘ ρ g =  ((linear_map.comp (f.ℓ) ((ρ g): M →ₗ[R]M  ) : M → M')) := rfl

def one (ρ : group_representation G R M) : ρ ⟶ ρ := 
{ ℓ         := linear_map.id,
  commute   := λ g, rfl
}

notation `𝟙` := one
end morphism

