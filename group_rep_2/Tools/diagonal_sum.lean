import data.fintype.basic
import algebra.big_operators
open_locale big_operators
open_locale classical
open finset
universes u v 
variables (X : Type u)[fintype X][decidable_eq X](R : Type v) [ add_comm_group R]
          (Y: Type )[fintype Y][decidable_eq Y]
/--
#  TODO ::    Ici c'est à reprendre au moment de l'integration 
-/

def blabla (φ : X × X → R) (p : finset (X × X)) :  {x | x ∈ p}  → X := 
begin 
    intros, rcases a, exact a_val.fst,
end


lemma ter (φ : X × X → R) (hyp : ∀ x : X × X, x.fst ≠ x.snd →  φ x = 0) :  
∑ y, φ  y =  ∑ y in filter {y : X × X| y.fst =y.snd} univ, φ y := 
begin 
    let p := {x : X × X | x.fst ≠  x.snd},
    rw ←  sum_sdiff (finset.subset_univ ( filter p finset.univ)),
    have : ∑ s in filter p univ, φ s = 0 ,
        apply sum_eq_zero,
        intros x hyper,  rw mem_filter at hyper, 
        exact hyp x hyper.2,
        rw this, rw add_zero,
        congr,
        ext, split, intros, rw mem_filter, rw mem_sdiff at a_1, simp,
        by_contradiction,
        have rr : a ∈ filter p univ,
            exact mem_filter.mpr ⟨mem_univ a, a_2⟩,
        exact a_1.right rr,
        intros, rw mem_sdiff,
        split,
            exact mem_univ _ ,
        intro, rw mem_filter at *,
        finish,
end



lemma GRAAL:  finset.filter (λ (a : X × X), {y : X × X | y.fst = y.snd} a ∧ a.snd = a.fst) finset.univ = 
            finset.filter ( {y : X × X | y.fst = y.snd}) finset.univ := 
    begin
        ext,split,
        intros, rw mem_filter,split, exact mem_univ a,
        rw mem_filter at a_1,
        rcases a_1,exact a_1_right.1,
        intros,rw mem_filter,split, exact mem_univ a,
        split,rw mem_filter at a_1, rcases a_1,
        exact a_1_right,
        rw mem_filter at a_1,rcases a_1,
        exact eq.symm(a_1_right),
end 

def f : X →   {y : X × X | y.snd = y.fst} := λ x, begin 
    exact ⟨ (x,x), rfl ⟩ ,
end
lemma f_ext (x : X) : (f X x).val = (x,x) := rfl
def g :  {y : X × X | y.snd = y.fst} → X := begin 
    intros, 
    rcases a, exact a_val.fst,
end

def G : X ≃  {y : X × X | y.snd = y.fst} := { 
  to_fun := f X,
  inv_fun := g X,
  left_inv := 
  begin 
    intro, exact rfl,
  end,
  right_inv :=
    begin 
        intro, unfold g, funext,  rcases x, 
        have : x_val.snd = x_val.fst,
            exact x_property,
            dsimp, unfold f, dsimp,
        have r : (x_val.fst, x_val.fst) = x_val,
        have rr : (x_val.fst, x_val.fst) = (x_val.fst, x_val.snd),
            ext, exact rfl,
            rw this, rw rr, simp, 
            congr, exact r, 
  end }
#check finset.sum_bij
lemma rrr ( a b : finset X)  : a = b → card a = card b := begin 
exact congr_arg (λ (a : finset X), card a),
end
lemma  sum_diagonal_one_eq_cardinal (R : Type v) [comm_ring R] :  (∑ (x : X × X), ite (x.snd = x.fst) (1 : R)  0)  = fintype.card X := 
begin 
    --- sum_permutation 
    rw finset.sum_ite,
    rw finset.sum_const_zero,
    rw finset.sum_const,
    rw add_zero,
    erw add_monoid.smul_eq_mul,rw mul_one,
    unfold_coes,
    rw congr_arg nat.cast _,
    rw fintype.card_congr (G X),
    erw fintype.card_of_subtype _,intros, split,intros,rw finset.mem_filter at a, exact a.2,
    intros, rw finset.mem_filter, split, exact finset.mem_univ x, exact a,
end


