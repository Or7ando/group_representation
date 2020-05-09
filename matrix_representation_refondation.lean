import linear_algebra.basic
import linear_algebra.basis
open linear_map
open is_basis
universe variables u v w 
namespace classical_basis
set_option trace.simplify.rewrite true
variables {G : Type u} {R : Type v} [group G] [comm_ring R] 
variables {X : Type w} [fintype X] [decidable_eq X] 
/-!
    Definition of classical basis of `X → R`. 
    `ε x = λ y, if x = y then 1 else 0`.
-/
def ε {R : Type v}[comm_ring R]{X : Type w}(x : X) [fintype X] [decidable_eq X] : 
        (X → R) := (λ y : X, if x = y then 1 else 0)
variable (x : X)
#check ε x x     -- premier probleme est-ce que je dois mettre X et R ?
                    -- C'est lourd

lemma epsilon_eq (x : X) : ε x x = (1 : R) :=   --- un meilleur nom ! 
begin 
    unfold ε,simp, 
end
/-!
    On va integrer les sommes pour obtenir une formule du style 
    pour f : X → R , f = ∑ λ x, f x * (ε  x) ! 
    C'est la décomposition dans la base ε ! 
-/
@[simp]lemma epsilon_ne ( x y : X)(HYP : ¬ y = x) : ε x y = (0 : R) := begin 
    unfold ε, split_ifs, rw h at HYP, trivial,
    exact rfl,
end 
@[simp]lemma smul_ite (φ : X → R) ( y : X) : (λ (x : X), φ x • (ε x y)) =  (λ x : X, if y = x then φ x else 0) := begin 
    funext,
    split_ifs, 
        rw h, rw epsilon_eq, exact mul_one (φ x),
        rw epsilon_ne x y h,
        exact mul_zero (φ x), 
end
notation `Σ` := finset.sum finset.univ 
lemma gen (φ : X → R) : φ  = Σ (λ (x : X), φ  x  • ε  x) := 
begin 
    funext y, 
    rw finset.sum_apply, 
    --change _ = Σ (λ x : X, φ x •  ε x y),
    erw smul_ite,
    erw finset.sum_ite_eq,
    split_ifs,exact rfl, 
    have R : y ∈ finset.univ, exact finset.mem_univ y, trivial,
end

   
#check is_basis R ε 
@[simp]lemma  test  (g : X → R)(s : finset X)(y ∈  s) : 
        finset.sum s (λ i : X, g i • (ε  i : X → R) ) y = finset.sum s (λ i : X, (g i • ε i) y) := 
begin exact finset.sum_apply (λ (i : X), R) (λ (i : X), g i • ε i) y,
    
end
@[simp]lemma classical_basis : is_basis R (λ x : X, (ε  x : X → R)) :=  --- c'est un peu chiant 
begin
    split,
    rw linear_independent_iff', intros s, intros φ, intros hyp, intros x, intros hyp_x, 
    rw function.funext_iff at hyp, specialize hyp x, 
    rw finset.sum_apply (λ (i : X), R) _ _ at hyp,
    change finset.sum s (λ y : X, φ y • (ε y x : R)) = 0   at hyp,
    rw smul_ite at hyp,
    erw finset.sum_ite_eq at hyp, split_ifs at hyp,assumption,
    rw eq_top_iff, rw submodule.le_def',
    intros φ, intros,
    rw gen φ,
    let p := (submodule.span R (set.range (λ (x : X), ε x))),
    apply submodule.sum_mem p,
    intros x, intros hyp,
    apply submodule.smul_mem p, 
    have r : ε x ∈ set.range (λ (t : X), ε t), 
        rw set.mem_range,
        use x,
    have rr :  set.range (λ (t : X), ε t) ⊆ ↑p,
        exact submodule.subset_span ,
    have rrr : ε x ∈ ↑p,
        exact set.mem_of_mem_of_subset r rr,
    exact rrr,
end   
end classical_basis
