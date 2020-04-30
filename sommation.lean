import linear_algebra.basic     
import data.fintype.basic
import algebra.big_operators
import data.finset algebra.big_operators
import data.set.function
import data.equiv.basic
open finset 
open equiv function fintype finset
universes u v w
namespace technical 
variables {α : Type u} {β : Type v}
lemma finset.prod_univ_perm [fintype α] [comm_monoid β] {f : α → β} (σ : perm α) :
  (univ : finset α).prod f = univ.prod (λ z, f (σ z)) :=
eq.symm $ prod_bij (λ z _, σ z) (λ _ _, mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _ H, σ.injective H) (λ b _, ⟨σ⁻¹ b, mem_univ _, by simp⟩)
end technical

def Sum {R : Type u}[add_comm_monoid R]{X : Type v}[fintype X](g : X → R) : R  := finset.sum (finset.univ) g 



lemma Sum_permutation  {R :Type u}[add_comm_monoid R]{X : Type v}[fintype X](g : X → R)(σ : equiv.perm X )
: finset.sum (finset.univ) g =   finset.sum (finset.univ) (λ z, g (σ z))  :=   @technical.finset.prod_univ_perm _ (multiplicative R) _ _ g σ

lemma Sum_add {R : Type} [ring R]{X : Type}[fintype X] (g : X → R)(h : X → R)  :  Σ  (h+g) = Σ  h + Σ  g  := begin
    exact multiset.sum_map_add,  --- 
end


lemma Sum.left_mul {R : Type} [ring  R]{X : Type}[fintype X] (g : X → R)  :  Sum  ( g) = Sum  g  := begin
    erw multiset.sum_map_mul_left,
end


lemma Sum.left_right {R : Type} [add_comm_monoid R]{X : Type}[fintype X] (g : X → R)(r : R) :  Σ  (r •   g ) =  (Σ  g) * r  := begin
    rw mul_comm, exact Sum.left_mul g r,
end


def Sum' (R : Type)[hyp1 : comm_ring R](X :Type)[hyp2 : fintype X] : (X → R) →ₗ[R] R := { to_fun := λ g, Σ g,
  add := begin intros, rw Sum_add,end,
  smul := begin intros, rw Sum.left_mul, exact rfl, end }
