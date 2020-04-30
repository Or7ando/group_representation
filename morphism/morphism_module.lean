import tactic
import group_representation
import morphism 
universe variables u v w w'

open linear_map
open morphism
variables {G : Type u} [group G] {R : Type v}[comm_ring R] 
 
namespace morphism
variables {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'] 
/-!
*    `Hom ρ π ` is the submodule of `Hom M M'` of `linear_map` that commute   
*     with the action i.e `ρ → π` 
-/
def Hom (ρ : group_representation G R M)(π : group_representation G R M') 
: submodule  R (M→ₗ[R] M') := { carrier := λ ℓ, ∀(g : G), ℓ ∘   ρ g  = π g  ∘   ℓ, 
  zero := begin 
        change ∀ g : G, 0 ∘ ρ g = π g ∘ 0,
        intros, ext,
        change  0 = (π g) 0,
        rw  (π g).map_zero,
    end,
  add := begin
        intros ℓ_1  ℓ_2, intros hyp_f hyp_g,
        change ∀ g : G, (ℓ_1+ℓ_2) ∘ _ = _ ∘ _ ,
        intros g,
        change (ℓ_1 ∘  (ρ g)) +  ℓ_2 ∘ _ = _ ,
        rw [hyp_f g , hyp_g g], 
        ext,
        change _ = π g ( ℓ_1 x + ℓ_2 x),
        rw (π g).map_add,
        exact rfl,
   end,
  smul := begin rintros c ℓ hyp, change ∀ g :G,   (( c • ℓ  ) ∘ _) = _ ,
                intro g, ext x, 
                change c • (( ℓ  ∘   ρ g )  x) = _,
                rw hyp g, change _ = π g ( c • ℓ _), 
                rw (π g).map_smul,
end }
def Hom' (ρ : group_representation G R M)(π : group_representation G R M') 
: submodule  R (M→ₗ[R] M') := { carrier := {ℓ | ∀(g : G), ℓ ∘   ρ g  = π g  ∘ ℓ}, 
  zero := 
    begin 
        change ∀ g , _,
        intros, ext,
        change  0 = (π g) 0,
        rw  (π g).map_zero,
    end,
  add := begin
        intros ℓ_1  ℓ_2, intros hyp_f hyp_g,
        change ∀ g, _  ,
        intros g,
        change (ℓ_1 ∘  (ρ g)) +  ℓ_2 ∘ _ = _ ,
        rw [hyp_f g , hyp_g g], 
        ext,
        change _ = π g ( _ + _),
        rw (π g).map_add,
        exact rfl,
   end,
  smul := begin rintros c ℓ hyp, change ∀ g ,   _ ,
                intro g, ext x, 
                change c • (( ℓ  ∘   ρ g )  x) = _,
                rw hyp g, change _ = π g ( c • ℓ _), 
                rw (π g).map_smul,
end }

variables (ρ : group_representation G R M)(π : group_representation G R M') 
def to_fun (g : G) : (Hom ρ π ) →ₗ[R] (Hom ρ π) := { to_fun := λ f, { val := _,
  property := _ }, 
  add := _,
  smul := _ }





def ℋom : group_representation G R (Hom ρ π ) := { to_fun := _,
  map_one' := _,
  map_mul' := _ }
end morphism 
