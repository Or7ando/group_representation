import data.complex.basic
import linear_algebra.basic
import linear_algebra.determinant
import analysis.complex.polynomial
import data.polynomial 
import tools.caracteristic.tools
open finset
universes u v w w'
variables 
          {R : Type u}[nonzero_comm_ring R]
          {A : Type v} [fintype A][decidable_eq A] 
          (M : matrix A A R)
          (N : matrix A A (polynomial R))   
open polynomial open matrix
open with_bot tools
open_locale big_operators

/-
  unfold car_matrix, split_ifs, rw eval_add, rw eval_C, rw eval_X, rw h, rw add_val, rw smul_val, rw one_val, rw mul_ite,
     rw mul_one, rw mul_zero,simp, rw eval_C,rw add_val, rw smul_val, rw one_val, rw mul_ite,split_ifs, rw mul_zero,rw add_zero,
-/



lemma eval_ite (r : R) (P Q : polynomial R) (φ : Prop) [decidable φ]: 
    eval r  (if  φ  then P  else Q)  = if φ then eval r P else eval r Q := 
    by split_ifs; exact rfl
    
#check if_congr
#check if_true

noncomputable def car_matrix : 
      matrix A A (polynomial R) := λ x y, if x=y then  C (M x y) + X else C (M x y)

namespace car_matrix
lemma eval (r : R) (i j : A): eval r (car_matrix M i j) = (M + r • 1) i j := 
begin 
    unfold car_matrix,  rw eval_ite, rw eval_add, rw eval_C, rw eval_X,
    rw add_val, rw smul_val, rw one_val, rw mul_ite, rw mul_one, rw mul_zero,
    rw add_ite, rw add_zero,
end

noncomputable def car_pol : polynomial R :=  det (car_matrix M) 
/-!
    We admit a theorem 
-/
-- monic_mul  monic_X_add_C

lemma degree_coeff (x  : A) : degree(car_matrix M x x) = 1  := 
begin 
    unfold car_matrix, split_ifs,  let g := @degree_C_le R  (M x x) _,
    rw degree_add_eq_of_degree_lt,
    exact degree_X, rw degree_X,refine (lt_iff_not_ge (degree (C (M x x))) 1).mpr _, intro, 
     let tr := le_trans a g,  let g := zero_le_one,
        have : 0 = 1,
            apply le_antisymm,
            exact g, exact (with_bot.coe_le rfl).mp tr, trivial, trivial,
end

lemma degree_coeff_ne {x y : A} (hyp : x ≠ y) : degree(car_matrix M x y) ≤ 0 := begin 
    unfold car_matrix, split_ifs, trivial, exact degree_C_le,
end
lemma degree_coef_lt_one {x y : A} (hyp : x ≠ y) : degree(car_matrix M x y) < 1 := 
begin 
    let g := degree_coeff_ne M hyp,
    refine lt_of_le_of_lt g _,apply  coe_lt_coe.mpr,
    exact zero_lt_one,
end
lemma  zero_le_one :  (0 : with_bot ℕ )  ≤ 1 :=
        begin     apply coe_le_coe.mpr,
            exact zero_le_one,
end
lemma degree_le_one (x y : A) : degree(car_matrix M x y) ≤ 1 := 
begin 
    by_cases x = y,
        let g := degree_coeff M x, rw ← h, rw g, exact le_refl 1,
        let g := degree_coeff_ne M h,
        exact le_trans g (zero_le_one),
end


/--

-/
lemma leading_coef (x : A) :  leading_coeff (car_matrix M x x) = 1 := 
begin
        apply (monic.def).mp ,
        unfold car_matrix,
        split_ifs, rw add_comm, apply monic_X_add_C, trivial,
end
/-- 
      Technical lemma 
-/

lemma car_monic (x : A) : monic (car_matrix M x x) := begin 
    unfold monic, exact leading_coef M x,
end


end car_matrix

namespace car_pol
open car_matrix equiv.perm

/-!
    Now we reconstruct the coeffcient of det_car the 
        ` Σ (σ ∈ perm A), sign σ  ×  ∏ (ℓ ∈ A) car_matrix M σ ℓ ℓ  


-/

lemma eval_sum  (φ : A → polynomial R) (r : R)  : eval r (Σ   φ ) =  Σ (λ a : A,(eval r (φ a))) := 
begin 
    rw finset.sum_hom finset.univ (polynomial.eval r),
end

lemma eval_prod (φ : A → polynomial R) (r : R) : eval r (finset.prod finset.univ φ) =  
finset.prod finset.univ (λ a : A,(eval r (φ a))) := 
begin 
    rw finset.prod_hom finset.univ (polynomial.eval r),
end

lemma   test (a : ℤ )(r : R) : eval r (a : polynomial R) = (a : R) := 
begin 
    rw int_cast_eq_C, rw eval_C,
end 


theorem eval_car_poly ( r : R) : eval r (car_pol M) = det (M+ r • 1) := begin 
    unfold det, unfold car_pol, unfold det,
    erw eval_sum, congr, ext σ ,
    rw eval_mul,
    rw eval_prod,
    rw int_cast_eq_C, rw eval_C, congr, ext,
    rw car_matrix.eval,
end
lemma perm_mul (σ : equiv.perm A) (P : polynomial R) : degree ((sign σ : polynomial R) * P) = degree P := begin
    rcases int.units_eq_one_or (sign σ), congr,
     rw h, erw int.cast_one, rw one_mul, 
     rw h,  
     erw int.cast_neg, erw int.cast_one,
     norm_cast,simp, 
end  

lemma equiv_not_id (σ  : equiv.perm A) (hyp : σ ≠ 1) : ∃ x : A, σ x ≠ x := begin 
    refine not_forall.mp _,
        intro, have : σ =1,
            ext, exact a x, trivial, 
end

lemma exists_le_one (σ  : equiv.perm A) (hyp : σ ≠ 1) : ∃ ℓ0 : A,  degree( car_matrix M (σ ℓ0 ) ℓ0 ) < 1:= begin 
    rcases (equiv_not_id σ hyp) with ⟨ℓ0,hyp_l ⟩,
    use ℓ0,
    let r := degree_coeff_ne M  hyp_l,
    refine lt_of_le_of_lt r _,
    apply  coe_lt_coe.mpr,
    exact zero_lt_one,
end


noncomputable def term_wihout  (σ : equiv.perm A) := 
     finset.prod univ (λ (x : A), car_matrix M (σ x) x)  

noncomputable def term  (σ : equiv.perm A) := 
    ((equiv.perm.sign σ) : polynomial R ) * finset.prod univ (λ (x : A), car_matrix M (σ x) x)


lemma degree_term_eq_degree_term_without  (σ : equiv.perm A ) : degree (term M σ ) = degree (term_wihout M σ ) :=  perm_mul _ _

lemma degree_term_wihout (σ : equiv.perm A) : if σ = 1 then  degree (term_wihout M σ) = fintype.card A else  degree (term_wihout M σ) < fintype.card A
:= begin
    split_ifs, rw h, {
            unfold term_wihout,
            exact prod_monic_one (finset.univ) (λ ℓ, car_matrix M  ℓ ℓ )(degree_coeff M ) (car_monic M),
        }, 
        {   
            unfold term_wihout,
            apply degree_prod_le_one_lt_card((λ ℓ, car_matrix M  (σ ℓ) ℓ )),
            intros ℓ, refine degree_le_one M _ _,
            rcases equiv_not_id (σ ) h with ⟨ℓ0 ,hyp_l0 ⟩ ,
            use ℓ0,
            exact degree_coef_lt_one M hyp_l0,
        },
end
lemma degree_term (σ : equiv.perm A) : 
if σ = 1 then  degree (term M σ) = fintype.card A else  degree (term M σ) < fintype.card A := 
begin 
    rw degree_term_eq_degree_term_without, exact degree_term_wihout M σ, 
end
lemma degree_term_id :  degree (term M (1 : equiv.perm A)) = fintype.card A := 
begin   
    let g := degree_term M (1 : equiv.perm A),
    split_ifs at g, exact g, trivial,
    
end
lemma degree_term_ne (σ : equiv.perm A) (hyp : 1 ≠ σ ) : degree (term M σ) < fintype.card A := 
begin 
    let g :=  degree_term M σ ,
    split_ifs at g, rw h at hyp,trivial, exact g,
end
lemma degree_car : degree (car_pol M) = fintype.card A := 
begin 
    unfold car_pol, unfold det,
    rw ← degree_term_id M, 
    apply  proof_strategy.car_pol_degree(term M), 
    rw degree_term_id M,
    exact degree_term_ne M,
    rw degree_term_id, exact bot_lt_some _,
end

theorem eigen_values_exist_mat (hyp : 0 < fintype.card A  ):  ∀ M : matrix A A ℂ ,  ∃ t : ℂ, det ( M + t •(1 : matrix A A ℂ )) = 0 
:= begin 
    intros M,
    let χ := car_pol M,
    let FTOA := @complex.exists_root χ,
    have : 0 < degree χ,
        erw  degree_car, apply coe_lt_coe.mpr,exact hyp,
    specialize FTOA this,
    rcases FTOA with ⟨ ζ,hyp⟩ ,
    use ζ,
    rw ←  eval_car_poly M ζ ,
    exact hyp,
end 
end car_pol