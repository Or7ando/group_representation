import .group_representation
import .morphism
universe variables u v w 
variables {G : Type u} {R : Type v} {M : Type w} [group G] [ring R] [add_comm_group M] [module R M] 

namespace stability  

variables {p : submodule R M} 
/--
  Technical lemma to deal with `submodule p` of `M`.
-/

lemma submodule_ext (x y : p) : (x : M) = (y : M)  → x = y := begin
          intros,rcases x,rcases y,congr; try {assumption},
end

lemma coersion₂ ( f g : M ≃ₗ[R] M) : ⇑ f ∘ ⇑ g = ⇑ (f * g) := rfl

/--
  Let `ρ : G →* M ≃ₗ[R] M` a representation. A submodule `p` of `M` is `ρ-stable` when : 
      `∀ g ∈ G, ∀ x ∈ p, ρ g x ∈ p`. It induce a `sub-representation`  : ` Res ρ  p : G →* p ≃ₗ[R] p `
-/ 
def stable_submodule (ρ : group_representation G R M)(p : submodule R M) :=  
                     ∀ g : G, ∀  x : p,  ρ g x ∈ p    --- better with x : M, x ∈ p → ρ g x ∈ p  ?   
variables {ρ : group_representation G R M}

/--
  Restriction map : `res ρ : G → (p → p)`. 
-/
def res  (stab : stable_submodule ρ p):  G → p → p  := λ g x, ⟨( ρ   g ) x, stab g x⟩

variables (stab : stable_submodule ρ p)(g : G)

lemma coersion (x : p) :   ((res stab g x) : M) = (ρ g : M ≃ₗ[R] M) (x : M) := rfl


lemma res_add (g : G) (x y : p) : res stab g (x+y) = res stab g x + res stab g y := begin
    apply submodule_ext, change ρ _ _ = _, 
    erw (ρ g).map_add, 
    exact rfl,
end 

lemma res_smul (g : G) (r : R) ( x : p) : res stab g ( r • x) = r • res stab g x := begin 
    apply submodule_ext, change ρ _ _ = _, erw (ρ g).map_smul, exact rfl,
end
/--
   `res` is linear map.  
-/
def res_linear (stab : stable_submodule ρ p) (g : G) : p →ₗ[R]p := { to_fun := res stab g,
  add := res_add  stab g,
  smul := res_smul stab g }
/--
  ` ∀ g :G, res ρ g` has an inverse given by ` res ρ g⁻¹`. 
-/

lemma res_mul (stab : stable_submodule ρ p ) (g1 g2 : G) : res stab (g1 * g2) = res stab g1 ∘ res stab g2 :=
 begin 
      
      ext, apply submodule_ext,  rw [ coersion, ρ.map_mul], exact rfl,

end
lemma res_one (stab : stable_submodule ρ p) : res stab 1 = id := 
begin 

  ext,apply submodule_ext,rw [coersion,ρ.map_one], exact rfl,

end
/--
  `res` is an `set` equivalence 
-/
def  res_equiv (h : stable_submodule ρ p) (g : G) :  (p ≃ p) :=   
{ to_fun := (res  h g),
  inv_fun := (res  h g⁻¹),
  left_inv := begin  
              intros x, apply submodule_ext,
              change (ρ _   *  _) x = _, rw ← ρ.map_mul,
                rw [inv_mul_self,
                    ρ.map_one ],  exact rfl,
               end
  , right_inv := begin 
               intros x,
               apply submodule_ext,
               change (ρ g * _) x = _,
               rw ←  ρ.map_mul,
               rw mul_inv_self, rw ρ.map_one, exact rfl,
  end }
/--
    We make `G → p ≃ₗ[R]p` 
-/
def res_equiv_linear (stab : stable_submodule ρ p) (g : G) : p ≃ₗ[R]p := { 
    .. res_linear stab g,
    ..  res_equiv stab g}


lemma res_equiv_coersion (stab : stable_submodule ρ p) (g : G)(x : p) : 
          (res_equiv_linear stab g) x = res stab g x:= rfl

/--
   the restriction representation `G →* p ≃ₗ[R]p`
-/
def Res (stab : stable_submodule ρ p) : group_representation G R p := {
   to_fun := res_equiv_linear stab,
  map_one' := begin 
                ext,apply submodule_ext, change (ρ 1) x = _,  rw ρ.map_one, 
                exact rfl,
                end, 

  map_mul' := begin intros g1 g2, 
                    ext, apply submodule_ext,
                    change  (ρ (g1 *  g2))  x = _ ,  rw  ρ.map_mul, 
                    exact rfl,
              end}
/-
  i have to study more the notion 
-/
theorem Res.apply (g : G) (x : p) : (Res stab g x : M) = ρ g x := rfl
/--
   make a morphism : `Res stab → ρ` 
-/

def res.subtype (stab : stable_submodule ρ p) : Res stab ⟶ ρ  := { 
    ℓ := submodule.subtype p,
    commute := by {intros g, exact rfl}
}
end stability