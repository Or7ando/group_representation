import data.fintype.basic
import algebra.big_operators
import data.set.function
import data.equiv.basic
open finset 
open equiv function fintype finset
universes u v 
variables {α : Type u} {β : Type v}

lemma finset.prod_univ_perm [fintype α] [comm_monoid β] {f : α → β} (σ : perm α) :
  (univ : finset α).prod f = univ.prod (λ z, f (σ z)) :=
eq.symm $ prod_bij (λ z _, σ z) (λ _ _, mem_univ _) (λ _ _, rfl)
  (λ _ _ _ _ H, σ.injective H) (λ b _, ⟨σ⁻¹ b, mem_univ _, by simp⟩)

lemma Sum_permutation  {R :Type u}[add_comm_monoid R]{X : Type v}[fintype X](g : X → R)(σ : equiv.perm X )
: finset.sum (finset.univ) g =   finset.sum (finset.univ) (λ z, g (σ z))  :=   @finset.prod_univ_perm _ (multiplicative R) _ _ g σ
