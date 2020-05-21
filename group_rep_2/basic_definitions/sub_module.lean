import .group_representation
import .morphism
universe variables u v w 
variables {G : Type u} {R : Type v} {M : Type w} [group G] [ring R] [add_comm_group M] [module R M] 

namespace stability  

variables {p : submodule R M} 
/--
  Technical lemma to deal with `submodule p` of `M`.
-/

lemma submodule_ext (x y : p) : (x : M) = (y : M)  → x = y := 
begin
  intros,rcases x,rcases y,congr, try {assumption},
end
/--
  Let `ρ : G →* M ≃ₗ[R] M` a representation. A submodule `p` of `M` is `ρ-stable` when : 
      `∀ g ∈ G, ∀ x ∈ p, ρ g x ∈ p`. It induce a `sub-representation`  : ` Res ρ  p : G →* p ≃ₗ[R] p `
-/ 
class stable_submodule (ρ : group_representation G R M)(p : submodule R M) :=  
                   (stability :  ∀ g : G, ∀  x : M, x ∈ p →   ρ g x ∈ p)    

/--
    `Trivial submodule` : `⊥` and `⊤` 
-/
def is_trivial (p : submodule R M) := (p = ⊤ ∨  p = ⊥)
/--
    `Irreducible ρ` : only `⊥` and `⊤` for ` ρ-stable submodule` 
-/
class Irreductible ( ρ : group_representation G R M)  :=
 (certif: ∀ (p : submodule R M)[stable_submodule ρ p], is_trivial p)


def Trivial (ρ : group_representation G R M)(p : submodule R M) [Irreductible ρ] [stable_submodule ρ p]:= 
                Irreductible.certif ρ  p



variables (ρ : group_representation G R M)

lemma stab [stable_submodule ρ p](g : G) {x : M} :  (x ∈ p )  →   (ρ g x ∈ p) :=  
stable_submodule.stability g x


lemma map' (g : G) [stable_submodule ρ p] : submodule.map (ρ g) p ≤  p := begin 
    rw submodule.le_def', intros x hyp, rw submodule.mem_map at hyp, rcases hyp with ⟨y,hyp_y ⟩,
    rw ←  hyp_y.2, 
    apply (stab ρ g), exact hyp_y.1, assumption,
end

lemma map (g : G) [stable_submodule ρ p] : submodule.map (ρ g) p = p := 
begin 
  apply le_antisymm, apply map',
  rw submodule.le_def', intros x hyp_x, rw submodule.mem_map, use (ρ g⁻¹ ) x,  split, 
  apply stab ρ g⁻¹, exact hyp_x, assumption, change (ρ g ⊚ ρ g⁻¹ ) x = _, 
  rw ← map_comp, rw mul_inv_self, rw ρ.map_one, exact rfl, 
end

/--
  Restriction map : `res ρ : G → (p → p)`. 
-/
def res  [stable_submodule ρ p] :  G → p → p  :=  λ g x, {
  val      := ρ g x, 
  property := stab ρ g x.property
  }


variables [stable_submodule ρ p]


lemma res_add (g : G) (x y : p) : res ρ g (x+y) = res ρ g x + res ρ  g y := 
begin
    apply submodule_ext, change ρ _ _ = _, 
    erw (ρ g).map_add, 
    exact rfl,
end 

lemma res_smul (g : G) (r : R) ( x : p) : res ρ  g ( r • x) = r • res ρ g x := 
begin 
    apply submodule_ext, change ρ _ _ = _,
    erw (ρ g).map_smul, 
    exact rfl,
end
/--
   `res` is linear map.  
-/
def res_linear [stable_submodule ρ p] (g : G) : p →ₗ[R]p := { 
  to_fun := res ρ  g,
  add    := res_add ρ  g,
  smul   := res_smul ρ  g }
/--
  ` ∀ g :G, res ρ g` has an inverse given by ` res ρ g⁻¹`. 
-/

lemma res_mul (g1 g2 : G) : (res ρ (g1 * g2) : p → p) = res  ρ  g1 ∘ (res ρ  g2) :=
 begin 
    ext, apply submodule_ext, change ρ (g1 * g2) x = _,
    erw ρ.map_mul, exact rfl,
end
lemma res_one  : (res ρ 1 : p → p) = id := 
begin 
  ext,apply submodule_ext, change ρ 1 x = _,
  erw ρ.map_one, exact rfl,
end

/--
   the restriction representation `G →* p ≃ₗ[R]p`
-/
def Res  : group_representation G R p := {
  to_fun   := res_linear ρ ,
  map_one' := begin  ext,apply submodule_ext, change (ρ 1) x = _,  rw ρ.map_one,  exact rfl, end, 
  map_mul' := 
   begin 
    intros g1 g2, 
    ext, apply submodule_ext,
    change  (ρ (g1 *  g2))  x = _ ,  rw  ρ.map_mul, 
    exact rfl,
  end
}
def res.subtype  : Res ρ  ⟶ᵣ ρ  := { 
  ℓ       := submodule.subtype p,
  commute := by {intros g, exact rfl}
}
end stability