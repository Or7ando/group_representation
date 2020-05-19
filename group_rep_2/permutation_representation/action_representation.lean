import basic_definitions.sub_module
import Tools.tools
import linear_algebra.matrix
import group_theory.group_action
import init.algebra.functions
--set_option trace.simplify.rewrite true   --- a reprednre peut etre un peu ! 
open_locale big_operators
namespace general
universes u v  w w' 
variables (G : Type u) (R : Type v) (X : Type w) [group G] [ring R]  [mul_action G X] 

/--
    Permutation representation : let `•` an action of `G` on `X`. Let `R` be a ring, 
    let `M = R → X` be the free-module over `M` of base `X`. For `v : R → X` and `g ∈ G` the formula  
    `ρ g v := g⁻¹ • v` define a permutation de representation.  
 -/

def rho  (g : G)  : (X → R) → (X → R)  := λ  v x,  v (g⁻¹ •  x)

def rho_linear (g : G) : (X → R) →ₗ[R] (X → R) := { 
  to_fun := rho G R X g,
  add := by { intros, exact rfl},
  smul := by {intros, exact rfl}
}

@[simp]lemma rho_apply (g : G)(v : X → R)(x : X) : rho G R  X g v x  = v (g⁻¹ • x) := rfl  

@[simp]lemma rho_mul (σ τ  : G) : rho G R X (σ * τ) = rho G R X σ  ∘  rho G R X τ := begin 
        ext v x, rw rho_apply, rw  mul_inv_rev, rw  mul_smul, exact rfl,    
end 
@[simp]lemma rho_one  : rho G R X (1 : G) = id := begin 
   ext x v, rw rho_apply, rw one_inv, rw one_smul, exact rfl,
end
@[simp]lemma rho_right_inv (g : G) : (rho G R X g : (X → R) →  (X → R)) ∘  (rho G R X g⁻¹) = id  := begin 
    rw ← rho_mul, rw mul_inv_self, rw rho_one,
end

@[simp]lemma rho_left_inv  (g : G) : (  rho G R X (g⁻¹ )  : 
(X → R) → (X → R) ) ∘    (rho G R X g : (X → R) → (X → R))  = id  :=  
begin 
    rw ← rho_mul, rw inv_mul_self, rw rho_one, 
end


def Perm : group_representation G R (X → R) := { 
  to_fun    :=  rho_linear G R X,
  map_one'  := 
    begin  
        unfold rho_linear,congr,
        exact rho_one G R X, 
    end,
  map_mul'  := 
    begin  
        unfold rho_linear, intros, congr,
        exact rho_mul G R X _ _,
    end 
}
variables (g : G) (x y : X → R)

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

@[simp]theorem action_on_basis (g : G)(x : X) : rho G R X g (ε x) = ε (g • x) := begin 
    funext y, simp,  
    unfold ε, 
    split_ifs, 
        {exact rfl},
        {rw [h, ← mul_smul,mul_inv_self,one_smul] at h_1, trivial},
        {rw [← h_1, ← mul_smul,inv_mul_self,one_smul] at h, trivial},
        {exact rfl},
end 
@[simp]theorem action_on_basis_apply (g : G) (x y : X) : rho G R X g (ε x) y = if g • x = y then 1 else 0 := 
begin simp, exact rfl,
   -- rw action_on_basis, exact rfl, 
end
@[simp]theorem trace (g : G) :  ∑ (x : X), rho G R X g (ε x) x =  fintype.card {x : X |  g • x = x } := 
begin simp, exact rfl,
    --have r :  (λ (x : X), rho G R X g (ε x) x) = λ x,if g • x = x then 1 else 0,
    --   funext, rw action_on_basis_apply,
    --rw r,
    --rw finset.sum_boole,simp, exact rfl, --- filter ? 
end
variables (g : G)
@[simp]lemma  Perm_ext (g : G) :  rho G R X g = (Perm G R X) g    := rfl  

end finite_action