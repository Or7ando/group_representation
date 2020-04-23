import .group_representation
import .sub_module
import linear_algebra.determinant
import linear_algebra.matrix
import group_theory.group_action
import init.algebra.functions
universes u v  w w' 
variables {G : Type u} (R : Type v) (X : Type w)
  [group G] [ring R]  [mul_action G X] 


/--
    Permutation representation : let `•` an action of `G` on `X`. Let `R` be a ring, 
    let `M = R → X` be the free-module over `M` of base `X`. For `v : R → X` and `g ∈ G` the formula  
    `ρ g v := g⁻¹ • v` define a permutation de representation.  
 -/

lemma add_ext  ( u v : X → R) (x : X) : (u+v) x = u x + v x := begin 
    exact rfl,
end 


def rho  (g : G)  : (X → R) → (X → R)  := λ  v x,  v (g⁻¹ •  x)



lemma mul_ext (r : R)( u : X → R) (x : X) : (r • u) x = r * u x := rfl

lemma rho_ext (g : G) (v : X → R) (x : X) : rho R X g v x = v (g⁻¹ • x) := rfl 

lemma rho_add  (g : G) (v1 v2 : X → R) : rho R X g ( v1+v2) = rho R X g v1 + rho R X g  v2 :=
begin 
    ext, rw rho_ext, rw add_ext, rw add_ext, exact rfl,
end

lemma rho_smul (g : G)(r : R)( v : X →  R ) : rho R X g (r • v) = r • rho R X g v := begin
    ext, rw rho_ext,rw mul_ext,exact rfl,
end

def rho_linear (g : G) : (X → R) →ₗ[R] (X → R) := { to_fun := rho R X g,
  add := rho_add R X g,
  smul := rho_smul R  X  g}

lemma rho_right_inv (g : G) : (rho R X g : (X → R) →  (X → R)) ∘  (rho R X g⁻¹) = id  := begin 
    ext v x, rw function.comp_apply, rw id, 
    rw rho_ext,rw rho_ext,rw inv_inv, rw ←  mul_smul,rw mul_inv_self, rw one_smul,
end
lemma rho_inv_inv (g : G) (v : X → R) (x : X) :    rho R X g v = rho R X g⁻¹ ⁻¹  v:= begin 
    rw inv_inv,
end
lemma rho_one  : rho R X (1 : G) = id := begin 
    ext,rw rho_ext,rw one_inv,rw one_smul, exact rfl,
end
lemma rho_left_inv  (g : G) : (  rho R X (g⁻¹ )  : 
(X → R) → (X → R) ) ∘    (rho R X g : (X → R) → (X → R))  = id  :=  
begin ext v  x, rw function.comp_apply, rw rho_ext, rw rho_ext, rw inv_inv, 
rw ←  mul_smul, rw inv_mul_self, rw one_smul, exact rfl, end

/--
    a linear equivalence is a structure that formalize `M ≃ₗ[R]M` : group of invertible 
    linear morphism  `f : M →ₗ M`  
-/
def rho_equiv (g : G) : (X → R) ≃ (X → R) := { to_fun := rho R X g,
  inv_fun := rho R X g⁻¹ ,
  left_inv :=  begin intros x,ext, rw rho_ext,rw inv_inv,rw rho_ext,rw ← mul_smul, rw inv_mul_self,
  rw one_smul,  end,
  right_inv := begin intros x,ext, rw rho_ext,rw rho_ext,rw inv_inv,rw ← mul_smul, rw mul_inv_self, 
  rw one_smul, end }

def rho_equiv_lin (g : G) : (X → R) ≃ₗ[R] (X → R) := {
   .. rho_linear R X g,   .. rho_equiv R X g
}

lemma rho_equiv_lin_ext ( g : G): ((rho_equiv_lin R X g) : (X → R) → (X → R) ) =  rho R X g  := rfl

def Permutation_representation : group_representation G R (X → R) := { 
  to_fun :=  rho_equiv_lin R X ,
  map_one' := begin ext, rw  rho_equiv_lin_ext, rw rho_one, exact rfl,  end,
  map_mul' := begin  intros g1 g2,ext, rw  rho_equiv_lin_ext, 
             rw rho_ext,  rw mul_inv_rev, rw mul_smul,  exact rfl,
end }