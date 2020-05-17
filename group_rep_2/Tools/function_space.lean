import .finite_dimensional_lemma
open linear_map is_basis
open_locale big_operators
universe variables v w 
namespace classical_basis 
--- TODO :: a quoi sert le namespace : smul_ite est déjà dans mathlib il vaut repérer où je l'utilise dans mon histoire !
---  
/--
    Definition of classical basis of `X → R`. 
    `ε x = λ y, if x = y then 1 else 0`.
-/
def ε {R : Type v}[comm_ring R]{X : Type w}(x : X) [fintype X] [decidable_eq X] : (X → R) := 
    λ y : X, if x = y then 1 else 0

variables {R : Type v}  [comm_ring R] 
          {X : Type w} [fintype X] [decidable_eq X] 
lemma epsilon_eq (x : X) : ε x x = (1 : R) := by unfold ε; simp

@[simp]lemma epsilon_ne ( x y : X)(HYP : ¬ y = x) : ε x y = (0 : R) := --- y'a t'il mieux ? une directe ite ? 
 begin 
    unfold ε, split_ifs, {rw h at HYP, trivial}, {exact rfl},
end 
@[simp]lemma smul_ite (φ : X → R) ( y : X) : (λ (x : X), φ x • (ε x y)) =  (λ x : X, if y = x then φ x else 0) := begin 
    funext, unfold ε, 
    change _ * _ = _, erw mul_ite,
    rw [mul_one,mul_zero],
    exact if_congr eq_comm rfl rfl, 
end
lemma gen (φ : X → R) : φ  = ∑ x  , φ  x  • (ε  x) := 
begin            
    funext y,    -- simp,
    rw finset.sum_apply, -- unfold ε,  simp,
    conv_rhs {
        apply_congr,skip,
        rw ε, simp,  
    },
    erw finset.sum_ite_eq',simp,
end

@[simp]lemma classical_basis : is_basis R (λ x : X, (ε  x : X → R)) :=  
begin
split, 
    {apply  linear_independent_finite,
        intros φ hyp t,
        rw   ←  (gen φ)  at hyp,
        rw hyp,exact rfl },
    {apply gen_finite,  exact λ φ,  ⟨ φ, gen φ⟩}
end  
end classical_basis