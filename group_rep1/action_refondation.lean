import .group_representation
import .sub_module
import matrix_representation_refondation
import linear_algebra.matrix
import group_theory.group_action
import init.algebra.functions
set_option trace.simplify.rewrite true
namespace general
universes u v  w w' 
variables {G : Type u} (R : Type v) (X : Type w) [group G] [ring R]  [mul_action G X] 

/--
    Permutation representation : let `•` an action of `G` on `X`. Let `R` be a ring, 
    let `M = R → X` be the free-module over `M` of base `X`. For `v : R → X` and `g ∈ G` the formula  
    `ρ g v := g⁻¹ • v` define a permutation de representation.  
 -/

def rho  (g : G)  : (X → R) → (X → R)  := λ  v x,  v (g⁻¹ •  x)

def rho_linear (g : G) : (X → R) →ₗ[R] (X → R) := { to_fun := rho R X g,
  add := by { intros, exact rfl},
  smul := by {intros, exact rfl}
  }

@[simp]lemma rho_apply (g : G)(v : X → R)(x : X) : rho R  X g v x  = v (g⁻¹ • x) := rfl  

@[simp]lemma rho_mul (σ τ  : G) : rho R X (σ * τ) = rho R X σ  ∘  rho R X τ := begin 
        ext v x, rw rho_apply, rw  mul_inv_rev, rw  mul_smul, exact rfl,    
end 
@[simp]lemma rho_one  : rho R X (1 : G) = id := begin 
   ext x v, rw rho_apply, rw one_inv, rw one_smul, exact rfl,
end
@[simp]lemma rho_right_inv (g : G) : (rho R X g : (X → R) →  (X → R)) ∘  (rho R X g⁻¹) = id  := begin 
    rw ← rho_mul, rw mul_inv_self, rw rho_one,
end

@[simp]lemma rho_left_inv  (g : G) : (  rho R X (g⁻¹ )  : 
(X → R) → (X → R) ) ∘    (rho R X g : (X → R) → (X → R))  = id  :=  
begin 
    rw ← rho_mul, rw inv_mul_self, rw rho_one, 
end

/--
    a linear equivalence is a structure that formalize `M ≃ₗ[R]M` : group of invertible 
    linear morphism  `f : M →ₗ M`  
-/
def rho_equiv (g : G) : (X → R) ≃ (X → R) := { to_fun := rho R X g,
  inv_fun := rho R X g⁻¹ ,
  left_inv :=  begin intros x,ext, change (rho R X g⁻¹ ∘ rho R X g ) x x_1 = x x_1, rw rho_left_inv , exact rfl,   end,
  right_inv := begin intros x,ext, erw ← function.comp_apply (rho R X g)  _, rw rho_right_inv, exact rfl, end }

def rho_equiv_lin (g : G) : (X → R) ≃ₗ[R] (X → R) := {
   .. rho_linear R X g,   .. rho_equiv R X g
}

@[simp]lemma rho_equiv_lin_ext ( g : G): ((rho_equiv_lin R X g) : (X → R) → (X → R) ) =  rho R X g  := rfl

def Perm : group_representation G R (X → R) := { 
  to_fun :=  rho_equiv_lin R X ,
  map_one' := begin  ext,simp, exact rfl, end,
  map_mul' := begin  intros,ext, simp,  exact rfl, end }
variables (g : G) (x y : X → R)
#check Perm R X  

example (g : G) (x y : X → R) (r : R) : true := begin 
        let ρ := @Perm G R X,
        have f : ρ 1 = 1,
            rw ρ.map_one,  
        have : ρ g (x+y) = ρ g x +ρ g y, 
            rw (ρ g).map_add,
        
        trivial,
        end
end general 
namespace finite_action
open classical_basis general
universes u v  w w' 
variables {G : Type u} (R : Type v) (X : Type w) [fintype X] [decidable_eq X][group G] [comm_ring R]  [mul_action G X] 
/-!
    Goal : study more the representation 
-/

#check @ε R _ X _ _ _
@[simp]theorem action_on_basis (g : G)(x : X) : rho R X g (ε x) = ε (g • x) := begin 
    funext y, simp,  
    unfold ε, 
    split_ifs, 
        {exact rfl},
        {rw [h, ← mul_smul,mul_inv_self,one_smul] at h_1, trivial},
        {rw [← h_1, ← mul_smul,inv_mul_self,one_smul] at h, trivial},
        {exact rfl},
end 
@[simp]theorem action_on_basis_apply (g : G) (x y : X) : rho R X g (ε x) y = if g • x = y then 1 else 0 := 
begin simp, exact rfl,
   -- rw action_on_basis, exact rfl, 
end
@[simp]theorem trace (g : G) :  Σ (λ (x : X), rho R X g (ε x) x) =  fintype.card {x : X |  g • x = x } := 
begin simp, exact rfl,
    --have r :  (λ (x : X), rho R X g (ε x) x) = λ x,if g • x = x then 1 else 0,
    --   funext, rw action_on_basis_apply,
    --rw r,
    --rw finset.sum_boole,simp, exact rfl, --- filter ? 
end
variables (g : G)
#check (Perm  R X).to_fun g 
@[simp]lemma  Perm_ext (g : G) : rho R X g  = (Perm  R X).to_fun g  := rfl  
@[simp]theorem Trace_perm (g : G) : 
    Σ (λ x, ((Perm R X).to_fun g) (ε x) x ) = fintype.card {x : X |  g • x = x }  :=  trace R  X g

end finite_action