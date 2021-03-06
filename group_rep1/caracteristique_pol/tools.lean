import data.polynomial
open finset
universes u v 
variables 
          {R : Type u}[nonzero_comm_ring R]
          {A : Type v} [fintype A][decidable_eq A] 
          (M : matrix A A R)
          (N : matrix A A (polynomial R))   
namespace tools
open polynomial 
open with_bot 
notation `Σ` := finset.sum finset.univ
open_locale big_operators
/-!
    We start by explaining the strategy.
    Let :  
    `(s : finset A)(φ :A → polynomial R)(a : A)`
    `(hyp : ∀ b : A, a ≠ b →  degree (φ b) < degree (φ a) )`
    `(hyp_not_nul : ⊥  < degree (φ a))`:        
    Then 
    `if a ∈ s then (degree (finset.sum s φ ) =  degree (φ a))`
            ` else degree (finset.sum s φ ) < (degree (φ a))` 
    The caracteristic polynomial is constuct as a product over permutation. 
    We analyse each term of the sum. 
        If `σ = id ` then the degree of the polynomial is `card A` else the degre is less (`<`) than `card A` 
    That permit to apply the next lemma.  
-/


namespace with_bot

end with_bot


lemma χ_degree_strategy (s : finset A)(φ :A → polynomial R)(a : A)
(hyp : ∀ b : A, a ≠ b →  degree (φ b) < degree (φ a) ) (hyp_not_nul : ⊥  < degree (φ a)):        

        if a ∈ s then (degree (finset.sum s φ ) =  degree (φ a)) else degree (finset.sum s φ ) < (degree (φ a)) :=
begin 
    apply (finset.induction_on s), {
        intros, let F :=  not_mem_empty a, split_ifs,
        rw finset.sum_empty, rw degree_zero, assumption,
    },
    {{
        intros ℓ s hyp_ℓ hyp_rec,
        let p1 := φ a,
        let p2 := finset.sum s φ ,
        split_ifs with H, 
            by_cases a = ℓ,
                {
                    rw sum_insert (by assumption),
                    rw ← h,
                    split_ifs at hyp_rec,
                        {
                            rw h at h_1, trivial,
                            },
                        {   rw add_comm,
                            apply degree_add_eq_of_degree_lt,exact hyp_rec,
                            },
                          
                },
                {
                    split_ifs at hyp_rec,
                    {
                        rw sum_insert (by assumption),rw ← hyp_rec,
                        apply degree_add_eq_of_degree_lt, rw hyp_rec,
                        exact hyp ℓ h,
                        },
                    {
                        rw sum_insert (by assumption),
                        let g := mem_of_mem_insert_of_ne H h, trivial,
                        },
                },
            split_ifs at hyp_rec,
            {   have : a ∈ insert ℓ s,
                    apply  mem_insert_of_mem  h, trivial,
                
            },
            {
                rw sum_insert (by assumption),
                have : a ≠ ℓ,
                    let g := mem_insert_self ℓ s,
                    intro, rw a_1 at H, trivial,
                specialize hyp ℓ this,
                apply lt_of_le_of_lt (degree_add_le (φ ℓ ) p2),
                apply  max_lt (hyp)(hyp_rec),
            },
    }},
end


/--
    A friend version. 
-/
lemma proof_strategy.car_pol_degree  (φ :A → polynomial R)(a : A)
(hyp : ∀ b : A, a ≠ b →  degree (φ b) < degree (φ a) ) 
(hyp_not_nul : ⊥  < degree (φ a)):        
       (degree (Σ  φ ) =  degree (φ a))  :=
begin 
    let g := χ_degree_strategy (finset.univ) φ a hyp hyp_not_nul,
    split_ifs at g, assumption,
    let h := mem_univ a, trivial,
end



theorem my_theo (a b : with_bot ℕ  ) : a ≤ b → a+1 ≤ b+1 := begin 
    intros,
    rcases  b, intros, rcases a,
    exact le_refl (none +1), 
    erw  le_bot_iff at a_1, rw a_1, 
    refine le_refl _, 
    rcases a, 
    exact bot_le,
    apply  some_le_some.mpr, apply add_le_add,
    apply some_le_some.mp a_1, exact le_refl 1,
end 
#check with_bot.some_lt_some


lemma  zero_le_one' :  (0 : with_bot ℕ )  ≤ 1 :=
        begin     apply coe_le_coe.mpr,
            exact zero_le_one,
end



lemma prod_monic (s : finset A)(φ : A → polynomial R)  (hyp : ∀ a : A, monic (φ a)) : 
                monic (finset.prod s  (λ x : A, φ x))  :=
 begin 
    apply (finset.induction_on s), { 
      erw prod_empty at  *, 
      exact leading_coeff_C _,
    },
    {
        intros ℓ  s hyp' hyp_rec,
        rw finset.prod_insert (by assumption),
        apply monic_mul, exact hyp ℓ, exact hyp_rec,
    },
 end


lemma degree_prod_monic (s : finset A)(φ : A → polynomial R)
(hyp_lc : ∀ ℓ : A, monic (φ ℓ )) :   
  degree (finset.prod s  (λ x : A, φ x)) =  finset.sum s ( λ x : A, degree (φ x)) := 
  begin 
        apply (finset.induction_on s), {
          rw prod_empty,
          exact degree_C (one_ne_zero), 
    },
    {
        intros ℓ  s hyp' hyp_rec,
        rw finset.prod_insert (by assumption), 
        rw finset.sum_insert (by assumption),
        let g := monic_mul (hyp_lc ℓ ) (prod_monic s φ hyp_lc) ,
        rw ← hyp_rec,
        apply degree_mul_eq',
        conv_lhs {
            erw  monic.def.mp (hyp_lc ℓ), rw one_mul,
            erw  monic.def.mp (prod_monic s φ hyp_lc),
        },
        exact one_ne_zero,
    },
  end   

theorem cast_with_bot   (a  : ℕ ) :  nat.cast (a) = (a: with_bot ℕ ) := begin 
    apply (nat.rec_on a),  {
        exact rfl,
    },
    intros ℓ  hyp_rec,
    change _ = ↑ℓ + ↑1,
    erw ← hyp_rec, exact rfl,
end
lemma prod_monic_one  (s : finset A)(φ : A → polynomial R)(hyp : ∀ ℓ : A, degree(φ ℓ ) = 1 ) 
(hyp_lc : ∀ ℓ : A, monic(φ ℓ) ) :   -- monic ! 
  degree (finset.prod s  (λ x : A, φ x)) =  card s :=
 begin 
    rw degree_prod_monic s φ  hyp_lc,
    let g := @finset.sum_const _ _ s _ 1,
    conv_lhs{
        apply_congr, skip,
        rw hyp x,
    },
    rw finset.sum_const,  rw add_monoid.smul_one, unfold_coes, rw some_eq_coe, refine cast_with_bot  _ ,

    
end 


lemma degree_prod_le_sum_degree (s : finset A)(φ : A → polynomial R)  : 
                degree (finset.prod s  (λ x : A, φ x)) ≤ finset.sum s ( λ x : A, degree (φ x)) :=
 begin apply (finset.induction_on s), {
          rw prod_empty, rw sum_empty,
          rw degree_one, exact le_refl 0,
          },
        intros ℓ s hyp_ℓ hyp_rec,
        rw sum_insert (by assumption), rw prod_insert (by assumption),
        exact le_trans (degree_mul_le _ _) (add_le_add_left' (hyp_rec)),
 end




theorem sum_le (s : finset A) (φ : A → (with_bot ℕ) ) (hyp : ∀ ℓ : A, φ ℓ ≤ 1)  :  
        finset.sum s φ ≤  card s := 
begin 
    apply (finset.induction_on s), {
        rw sum_empty, rw card_empty, exact le_refl 0,
    },
    intros ℓ s hyp_l hyp_rec,
    rw sum_insert (by assumption), rw card_insert_of_not_mem(by assumption), rw coe_add, rw add_comm,
    apply add_le_add' hyp_rec (hyp ℓ ),
end

lemma prod_degree_one_le_card (s : finset A)(φ : A → polynomial R) (hyp : ∀ ℓ : A, degree(φ ℓ ) ≤  1 ) :
    degree (finset.prod s  (λ x : A, φ x)) ≤ card s := begin 
        apply le_trans (degree_prod_le_sum_degree s φ),
        apply sum_le  , exact hyp,
end 



lemma le_add_compensation (a : ℕ) { b c d : with_bot ℕ} : (a : with_bot ℕ ) + c ≤  b +d  →  b ≤ a →  c ≤ d := 
begin 
    intros hyp1 hyp2 , 
    have r : b+d ≤  a + d,
        exact add_le_add_right' hyp2,
    have : (a : with_bot ℕ ) + c ≤  a + d, 
        apply le_trans (hyp1) (r),
    rcases c, exact bot_le,
    rcases d, erw le_bot_iff at this, trivial,
    rw ← some_eq_coe at  * ,
    erw ← coe_add at this, erw ← coe_add at this,
    let F := coe_le_coe.mp this,
    apply coe_le_coe.mpr,
    exact (add_le_add_iff_left a).mp F,
end
/-!
    The last technical lemma 
-/
example (a b: ℕ ): a = b →  a ≤ b := begin 
library_search,
end
lemma add_eq_bot (a : ℕ ) (b : with_bot ℕ ) : (a : with_bot ℕ ) + b = ⊥  →   b = ⊥  :=
begin 
    cases b, intros,  rw none_eq_bot, intros, rw some_eq_coe at a_1, rw ← coe_add at a_1,  finish,
end
#check with_bot.
--by cases a; cases b; simp [none_eq_bot, some_eq_coe, coe_add.symm]
lemma ert (a b : ℕ) : (a = b ) → (a : with_bot ℕ ) = b := begin 
  intros,exact congr_arg coe a_1,
end

lemma tre (a b : ℕ ) : (a : with_bot ℕ ) = b → a = b := begin 
  intros,exact option.some_inj.mp a_1,
end
lemma left_cancel ( a : ℕ ) {b c : with_bot ℕ } : ↑a + b = a + c → b = c := begin 
    intros, 
    rcases b, rcases c, exact rfl, rw none_eq_bot  at a_1,
    rw add_bot at a_1, rw some_eq_coe at a_1, let g := (add_eq_bot a) c, 
    let h :=  eq.symm a_1,
    specialize g h, trivial, rw some_eq_coe at a_1, rw ← coe_add at a_1,cases c, finish, 
    rw some_eq_coe at a_1, rw ← coe_add at a_1, let k := tre (a+b) (a+c) a_1,
    rw some_eq_coe , rw some_eq_coe,
    apply ert,
    apply eq_of_add_eq_add_left k,
end 
theorem proof_stra (a : ℕ) { b c d : ℕ} :   a ≤ c → b ≤ d →  (a+ b = c +d → (a=c ∧ b = d)) :=
begin
    intros,split, apply le_antisymm, assumption,
    apply (add_le_add_iff_left b).mp, 
    conv_rhs {
        rw add_comm,
        rw a_3, rw add_comm,
    },
    apply (add_le_add_iff_right c).mpr , assumption,
    apply le_antisymm, assumption,
    apply (add_le_add_iff_left a).mp,
    conv_rhs  {
        rw a_3,
    },
    apply (add_le_add_iff_right d).mpr , assumption,
end  


/--
        I use proof_strategy 2 
-/
theorem q_card_insert_eq_card (s : finset A) (φ : A → (with_bot ℕ) )  
(hyp : ∀ ℓ : A, φ ℓ ≤ 1) (ℓ0 ∉ s ):  
 finset.sum (insert ℓ0 s)  φ = card (insert ℓ0 s) → finset.sum s  φ = card  s := 
 begin 
     rw sum_insert(by assumption),
    rw card_insert_of_not_mem(by assumption), rw [coe_add, add_comm], intros  hyp_s,
    apply le_antisymm( sum_le s φ hyp),
    have pre_strat :  ↑1 + ↑(card s)   =   φ ℓ0 + finset.sum s (λ (x : A), φ x),
        rw add_comm, rw ← hyp_s, rw add_comm,
    apply  le_add_compensation 1 (le_of_eq (pre_strat)),
    exact (hyp ℓ0), 
 end



theorem jenesaispas (s : finset A) (φ : A → (with_bot ℕ) )  
(hyp : ∀ ℓ : A, φ ℓ ≤ 1) : 
 finset.sum s φ = card s → (∀ ℓ : A, ℓ ∈ s → φ ℓ = 1) := 
 begin 
    apply (finset.induction_on s), {
        rw sum_empty, intros, let g := not_mem_empty ℓ , trivial,
    },
    {   
        intros ℓ s hyp_l hyp_rec,intros,
        
        by_cases ℓ_1 = ℓ,{ let h' := h,
            by_cases (finset.sum s φ = ↑(card s)),{
                rw [sum_insert(by assumption),card_insert_of_not_mem(by assumption), coe_add] at a,
            intros,rw h',
                rw h at a, rw add_comm at a, refine left_cancel (card s) a ,
            },
            let pre_strat := q_card_insert_eq_card s φ hyp ℓ hyp_l a,trivial,
            },
        {
            let  p := mem_of_mem_insert_of_ne a_1 h,
            let pre_strat := q_card_insert_eq_card s φ hyp ℓ hyp_l a,
            specialize hyp_rec pre_strat, exact hyp_rec ℓ_1 p,
        },
    },
 end





theorem det_card_term_'11 ( s: finset A) (φ : A → polynomial R)
(hyp : ∀ ℓ : A, degree(φ ℓ ) ≤ (1 : with_bot ℕ  ))  :
    degree (finset.prod s  (λ x :A, φ x)) =  card s → (∀ ℓ : A, ℓ ∈ s → degree (φ ℓ ) = 1)  :=
begin 
    let je := jenesaispas s (λ x, degree (φ x)) hyp,
    intros,
    have rr :  finset.sum s (λ x, degree (φ x))  = card s,
        apply le_antisymm,{
            apply sum_le s , exact hyp,
        },
        {
            rw ← a,      
            exact degree_prod_le_sum_degree s φ,
        },
    exact je rr ℓ  a_1,
 end


theorem degree_prod_le_one_lt_card (φ : A → polynomial R)
(hyp : ∀ ℓ : A, degree(φ ℓ ) ≤ 1 ) 
(hyp_lc : ∃  ℓ0 : A, degree (φ ℓ0) < 1) :
    
    degree (finset.prod finset.univ  (λ x :A, φ x)) <  fintype.card A := 

begin 
    by_contradiction contra, push_neg at contra,
    let g := det_card_term_'11 (finset.univ) φ hyp,
    have : ↑(fintype.card A) = degree (finset.prod univ (λ (x : A), φ x)),
        apply le_antisymm (by assumption),
            apply le_trans (degree_prod_le_sum_degree (finset.univ) φ),
            apply sum_le ,
            exact hyp,
        rcases hyp_lc with ⟨ ζ, j⟩, 
        specialize g (eq.symm this) ζ (mem_univ _),
        rw g at j,exact lt_irrefl 1 j,
end



end tools









/-
  unfold car_matrix, split_ifs, rw eval_add, rw eval_C, rw eval_X, rw h, rw add_val, rw smul_val, rw one_val, rw mul_ite,
     rw mul_one, rw mul_zero,simp, rw eval_C,rw add_val, rw smul_val, rw one_val, rw mul_ite,split_ifs, rw mul_zero,rw add_zero,
-/
