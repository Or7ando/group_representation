import data.fintype.basic
import algebra.big_operators
open_locale big_operators
open_locale classical
open finset
universes u v 
variables (X : Type u)[fintype X][decidable_eq X](R : Type v) [ add_comm_group R]
          (Y: Type )[fintype Y][decidable_eq Y]
/--
#  But  ::   ∑ (x : X × X), ite (x.snd = x.fst) (1 : R)  0  = fintype.card X
-/

def f : X →   {y : X × X | y.snd = y.fst} := λ x, begin 
    exact ⟨ (x,x), rfl ⟩ ,
end
lemma f_ext (x : X) : (f X x).val = (x,x) := rfl
def g :  {y : X × X | y.snd = y.fst} → X := begin 
    intros, 
    rcases a, exact a_val.fst,
end

def G : X ≃  {y : X × X | y.snd = y.fst} := { 
  to_fun    := f X,
  inv_fun   := g X,
  left_inv  := begin intro, exact rfl, end,  
  right_inv :=
    begin 
        intro, unfold g, unfold f,  rcases x, dsimp,
        congr,ext, exact rfl, exact symm (x_property),
    end }
lemma  sum_diagonal_one_eq_cardinal (R : Type v) [comm_ring R] :  (∑ (x : X × X), ite (x.snd = x.fst) (1 : R)  0)  = fintype.card X := 
begin 
    rw finset.sum_ite,
    rw finset.sum_const_zero,rw add_zero,
    rw finset.sum_const,
    
    erw add_monoid.smul_eq_mul,rw mul_one,
    unfold_coes,
    apply congr_arg nat.cast _,
    rw fintype.card_congr (G X),
    erw fintype.card_of_subtype _,
    intros, split,
        {intros,rw finset.mem_filter at a, exact a.2},
        {intros, rw finset.mem_filter, split, exact finset.mem_univ x, exact a},
end


