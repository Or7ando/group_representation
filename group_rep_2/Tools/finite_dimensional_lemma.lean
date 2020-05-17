import linear_algebra.basic
import linear_algebra.basis
open linear_map
open is_basis
universe variables u v w 
variables {R : Type v}  [comm_ring R] 
          {X : Type w} [fintype X] [decidable_eq X] 

open_locale big_operators
/--
    change a map by zero outside a `finset s`.  
-/
def updapte_with_zero ( φ : X → R) (s : finset X) : X → R := λ x, if x ∈ s then φ x else 0
/--
   `(updapte_with_zero φ s) x • B x = if x ∈ s then  φ x • B x else 0` 
-/
lemma updapte_with_zero_smul ( φ : X → R) (s : finset X) (M : Type u)[add_comm_group M] [ module R M] (B : X → M) :
(λ x : X, (updapte_with_zero φ s) x • B x) = (λ x : X, if x ∈ s then  φ x • B x else 0) := 
begin 
    funext, unfold updapte_with_zero,split_ifs, exact rfl,
    rw zero_smul, 
end
/--
    Helper for finite linear_independance 
    if `∀ φ : X → R,  (∑  x, φ x • B x = 0) → ∀ x : X, φ x = 0 )` then  `linear_independent R B`
-/
variables ( φ : X → R) 
lemma linear_independent_finite (M : Type u)[add_comm_group M] [ module R M] (B : X → M) : 
(∀ φ : X → R, (∑  x, φ x • B x = 0) → ∀ x : X, φ x = 0 )  →  linear_independent R B := 
begin 
    intros hyp_ind,
    rw linear_independent_iff',     
    intros s φ hyp x hyp_x, 
    --let F := hyp_ind φ, 
    specialize hyp_ind (updapte_with_zero φ s), rw updapte_with_zero_smul at hyp_ind,
    have R : ∑ x, ite (x ∈ s) (φ x • B x) 0 = ∑ i in  s, φ i • B i,
        rw finset.sum_ite, rw finset.sum_const_zero, rw add_zero,
        congr, exact finset.univ_inter s,
    rw hyp at R,
    specialize hyp_ind R x,rw ← hyp_ind,
    unfold updapte_with_zero,
    split_ifs,exact rfl,
end
/--
    Helper for finite span 
    if `∀ m :  M, ∃ φ : X → R, m =  ∑  x , (φ x) • (B x)` then
     `submodule.span R (set.range B) = ⊤`
-/
lemma gen_finite (M : Type u)[add_comm_group M] [ module R M] (B : X → M) : 
(∀ m :  M, ∃ φ : X → R, m =  ∑  x , (φ x) • (B x)) → submodule.span R (set.range B) = ⊤ := 
begin 
    intros hyp,rw eq_top_iff, rw submodule.le_def',
    intros m, intros,
    specialize hyp m,
    rcases hyp with ⟨φ , hyp_phi ⟩,
    rw hyp_phi,
    let p := submodule.span R (set.range B),
    apply submodule.sum_mem p ,
    intros x, intros,
    apply submodule.smul_mem p, apply submodule.subset_span, apply set.mem_range_self,
end 