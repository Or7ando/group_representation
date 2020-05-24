import .group_representation 
import algebra.module
universe variables u v w w' w'' w'''

open linear_map 
/--
  a morphism `f : ρ ⟶ᵣ π` between representation is a linear map `f.ℓ : M(ρ) →ₗ[R] M(π)` satisfying 
    `f.ℓ ∘   ρ g  = π g  ∘   f.ℓ` has function on `set`. 
-/
structure morphism  {G : Type u} [group G] {R : Type v}[ring R] 
                    {M : Type w}  [add_comm_group M] [module R M]
                    {M' : Type w'} [add_comm_group M'] [module R M'] 
                    (ρ : group_representation G R M) 
                    (π : group_representation G R M') 
  : Type (max w w') := 
      (ℓ       : M →ₗ[R] M')
      (commute : ∀(g : G), ℓ ⊚   ρ g  = π g  ⊚  ℓ) 

infixr ` ⟶ᵣ `:25 := morphism 

namespace morphism
variables {G : Type u} [group G] {R : Type v}[ring R] 
          {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'] 
          {ρ : group_representation G R M} 
          {ρ' : group_representation G R M'} 

@[ext]lemma ext ( f g : ρ ⟶ᵣ ρ') :  f.ℓ  = g.ℓ  → f = g := 
begin 
    intros, 
    cases f,cases g, congr'; try {assumption},
end

instance : has_coe_to_fun ( ρ ⟶ᵣ ρ') := ⟨_,λ f, f.ℓ.to_fun⟩  

lemma coersion (f : ρ ⟶ᵣ ρ') : ⇑f = (f.ℓ) := rfl

theorem commute_apply ( f : ρ ⟶ᵣ  ρ') (x : M) (g : G) : f ( ρ g x) = ρ' g (f x ) := 
begin 
      change (f.ℓ  ⊚  ρ g ) x = _,
      rw f.commute, exact rfl,
end


def is_invariant (ρ : group_representation G R M) (ρ' : group_representation G R M') 
 (ℓ : M →ₗ[R] M') := ∀(g : G), ℓ ⊚ ρ g   =  ρ' g   ⊚  ℓ

/--
  a constructor of morphism 
-/
def to_morphism  
(ℓ : M →ₗ[R] M') (commute : is_invariant ρ ρ' ℓ )  : ρ ⟶ᵣ ρ'  := { 
  ℓ       := ℓ ,
  commute := λ _, commute _
}
@[simp] lemma to_morphism_coe 
(ℓ : M →ₗ[R] M') (commute : is_invariant ρ ρ' ℓ)
: (to_morphism ℓ commute).ℓ = ℓ := rfl

@[simp]lemma of_morphism (f : ρ ⟶ᵣ ρ'  ) : is_invariant ρ ρ' f.ℓ  := λ g, f.commute g 

/--
  The identity morphism 
-/
def one (ρ : group_representation G R M) : ρ ⟶ᵣ ρ := 
{ ℓ         := linear_map.id,
  commute   := λ g, rfl
}

notation `𝟙` := one

instance : inhabited(ρ ⟶ᵣ ρ ) := { default := 𝟙 ρ }
end morphism


namespace morphism_module
open morphism linear_map
variables {G : Type u} [group G] {R : Type v}[comm_ring R] 
          {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M']
          {ρ : group_representation G R M}
          {ρ'  : group_representation G R M'}
variables {M'' : Type w''} [add_comm_group M''] [module R M'']

lemma comp_left_distrib (a : M' →ₗ[R]M'')(b c : M →ₗ[R]M') : a ⊚ (b + c) = a ⊚ b + a ⊚ c := begin 
    intros, ext x, erw map_add, exact rfl,
end
lemma comp_smul (r : R) (a : M' →ₗ[R]M'')(b  : M →ₗ[R]M') : a ⊚  (r • b) = r • (a ⊚ b) := 
begin 
    intros,ext,erw map_smul, exact rfl,
end
variables (r : R)
variables (f h : ρ ⟶ᵣ ρ')

def add : ρ ⟶ᵣ  ρ' := { 
  ℓ       := f.ℓ + h.ℓ ,
  commute := 
    begin  
      intros g, rw comp_left_distrib, rw ← f.commute, rw ← h.commute,
       ext, exact rfl,
    end 
  }
instance : has_add (ρ ⟶ᵣ ρ') := ⟨add⟩  
@[simp] lemma add_coe :  (f+h).ℓ = f.ℓ + h.ℓ := rfl
def neg : ρ ⟶ᵣ ρ' := {
  ℓ       := - f.ℓ, 
  commute := 
    begin
       intros g,  ext, change - (f.ℓ  ⊚  ρ g) x = _, erw f.commute,
       change _ = (ρ' g) (- _),
       erw (ρ' g).map_neg,   exact rfl,
    end
  }
instance : has_neg(ρ ⟶ᵣ ρ') := ⟨neg⟩
@[simp] lemma neg_coe :  (-f).ℓ = -f.ℓ := rfl
def zero : ρ ⟶ᵣ ρ' := { ℓ := 0, commute := begin intros g,  ext, simp,end}
instance : has_zero (ρ ⟶ᵣ ρ') := ⟨zero⟩   
@[simp] lemma zero_coe :  (0 : ρ ⟶ᵣ ρ').ℓ = 0 := rfl

instance : add_comm_group (ρ ⟶ᵣ ρ') := { 
  add           := add   ,
  add_assoc     := begin  intros, apply morphism.ext, repeat {rw add_coe}, rw add_assoc, end,
  zero          := 0,
  zero_add      := begin intros,apply morphism.ext, erw add_coe, rw zero_coe, rw zero_add, end,
  add_zero      := begin intros,apply morphism.ext, erw add_coe, rw zero_coe,rw add_zero,  end,
  neg           := neg ,
  add_left_neg  := begin intros,apply morphism.ext, erw add_coe, rw neg_coe, simp, end,
  add_comm      := begin intros,apply morphism.ext, erw add_coe, rw add_comm, exact rfl,end, 
}

def smul (r : R) (f : ρ ⟶ᵣ ρ') : ρ ⟶ᵣ ρ' := { 
  ℓ       := r • f.ℓ ,
  commute :=  
    begin 
      intros g, ext, 
      change r •( (f.ℓ ⊚  ρ g) x) = ρ' g (r • f.ℓ x), 
      rw f.commute, erw (ρ' g).map_smul, exact rfl,
    end
}
instance : has_scalar R (ρ ⟶ᵣ ρ') := ⟨ smul ⟩ 
@[simp] lemma coe_smul (r : R):( r • f).ℓ = r • f.ℓ := rfl
instance : module R (ρ ⟶ᵣ ρ') := { smul := smul,
  one_smul  := begin intros, apply morphism.ext, rw coe_smul, rw one_smul, end,
  mul_smul  := begin intros, apply morphism.ext, repeat {rw coe_smul}, rw mul_smul,end,
  smul_add  := begin intros, apply morphism.ext, repeat {rw coe_smul, rw add_coe}, rw smul_add, exact rfl,  end,
  smul_zero := begin intros, apply morphism.ext, repeat {rw coe_smul, rw zero_coe}, rw smul_zero,   end,
  add_smul  := begin intros, apply morphism.ext, repeat {rw coe_smul, rw add_coe}, rw add_smul,exact rfl,  end,
  zero_smul := begin intros, apply morphism.ext, repeat {rw coe_smul, rw zero_coe}, rw zero_smul,   end }

instance : is_add_monoid_hom (@morphism.ℓ  G _ R _ M _ _ M' _ _ ρ ρ' ) := { 
  map_add  := add_coe,
  map_zero := zero_coe }
end morphism_module

namespace Ring
variables {G : Type u}[group G]   {R : Type v}[comm_ring R] {M : Type w} 
          [add_comm_group M] [module R M]  
          {ρ : group_representation G R M}
          (f h : ρ ⟶ᵣ ρ )
open morphism morphism_module
/-
  Make an R algebra ? subalgebra of sub.type ! To check 
-/
def mul : ρ ⟶ᵣ  ρ := {
  ℓ       := f.ℓ ⊚  h.ℓ ,
  commute := 
    begin  
      intros g, 
      rw [comp_assoc, h.commute,  ← comp_assoc,  f.commute,  comp_assoc],
    end 
}
instance : has_mul (ρ ⟶ᵣ ρ ) := ⟨mul ⟩ 
@[simp] lemma mul_coe : ( f * h).ℓ = f.ℓ ⊚  h.ℓ  := rfl 
def one : ρ ⟶ᵣ ρ := { ℓ := 1, commute := begin intros g,  ext, simp,end}
instance : has_one (ρ ⟶ᵣ ρ) := ⟨one⟩   
@[simp] lemma one_coe :  (1 : ρ ⟶ᵣ ρ).ℓ = 1 := rfl
instance : ring (ρ ⟶ᵣ ρ ) := by refine { add := add,
  add_assoc     := add_assoc,
  zero          := zero,
  zero_add      := zero_add,
  add_zero      := add_zero,
  neg           := neg,
  add_left_neg  := add_left_neg,
  add_comm      := add_comm,
  mul           := mul,
  mul_assoc     := begin intros, apply morphism.ext, repeat {rw mul_coe}, rw comp_assoc,  end,
  one           := one,
  one_mul       := begin intros, apply morphism.ext, erw mul_coe, erw one_coe, erw id_comp,   end,
  mul_one       := begin intros, apply morphism.ext, erw mul_coe, erw one_coe, erw comp_id,   end,
  left_distrib  := begin intros, apply morphism.ext, repeat {erw mul_coe, erw add_coe}, rw comp_left_distrib, exact rfl,  end,
  right_distrib := begin intros, apply morphism.ext, erw mul_coe end, 
}

notation `𝟙` := one

end Ring
namespace illustration 
variables {G : Type u}[group G]   {R : Type v}[comm_ring R] {M : Type w} 
          [add_comm_group M] [module R M]  
          {ρ : group_representation G R M}
          (f g : ρ ⟶ᵣ ρ ) (r : R)
example :  f + g  = g + f := add_comm f g 

example : (f + g).ℓ = f.ℓ + g.ℓ := by simp 
open_locale big_operators
-- il nous faut une instance

lemma sum_coe (X : Type)[fintype X][decidable_eq X] (φ : X → (ρ ⟶ᵣ ρ)) :   (∑ x, φ x).ℓ  =  (∑ x, (φ x).ℓ ) :=
begin 
  rw @finset.sum_hom _ _ _ _ _ (finset.univ) φ morphism.ℓ  _ , --- ici c'est moyen car faut vraiment preciser l'instance !
end

lemma sum_apply (X : Type)[fintype X][decidable_eq X] (φ : X → (ρ ⟶ᵣ ρ)) (m : M) :  (∑ x, φ x).ℓ   m =  ∑ x, (φ x).ℓ   m := 
begin 
  erw ← sum_apply,
  rw sum_coe,
end
end illustration

namespace Projector 
open Ring 
variables {G : Type u}[group G]   {R : Type v}[comm_ring R] {M : Type w} 
          [add_comm_group M] [module R M]  
          {ρ : group_representation G R M}
          (f  : ρ ⟶ᵣ ρ ) (r : R)

/--
  I don't know if it s a good definition. 
-/
class is_projector : Prop := 
(idem : f * f = f) 

@[simp]lemma idem : is_projector f ↔  f * f = f := 
begin 
  split, intros, rw  a.idem, intros, use a,
end 

lemma is_projector_ext : is_projector f ↔ f.ℓ ⊚  f.ℓ = f.ℓ  := 
begin 
  split,intros, rw ← mul_coe, erw (idem f).mp a, intros, apply (idem f).mpr, 
  apply morphism.ext, rw mul_coe, exact a,
end   

instance is_projector_zero : is_projector (0 : ρ ⟶ᵣ ρ )   := (idem 0).mpr $ zero_mul _
instance is_projector_one  : is_projector (1 : ρ ⟶ᵣ ρ )   := (idem 1).mpr $ one_mul _ 

def irreductible :=  ∀ f : ρ ⟶ᵣ ρ , (is_projector f ↔ (f = 0 ∨ f = 1))

end Projector 

#lint