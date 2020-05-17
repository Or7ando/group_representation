import linear_algebra.determinant
import linear_algebra.matrix
open linear_map
notation f ` ⊚ `:80 g:80  := linear_map.comp f g    
universe variables u v w  w'
open matrix
open_locale big_operators matrix

variables {R : Type v} [comm_ring R] 
variables {X : Type w} [fintype X] [decidable_eq X] 
variables {Y : Type w} [fintype Y] [decidable_eq Y] 
variables {Z : Type w} [fintype Z] [decidable_eq Z] 
/-! 
   Study of the operation `to_matrix`.
   The file contain the classical operation of this function.     
-/
lemma proof_strategy (A B : matrix X Y R) : to_lin A = to_lin B → A = B :=
begin 
    intro hyp,
    have RR : to_matrix (to_lin A) = to_matrix (to_lin B),
        congr',
    iterate 2 {rw  to_lin_to_matrix  at RR},
    exact RR,   
end
/--
    `(a * b) • M = a • (b • M)`
-/
lemma mul_smul_mat (a b : R ) (M : matrix X X R ) : (a * b) • M = a • (b • M) :=
begin
    apply matrix.ext, intros, exact mul_smul a b (M i j),
end
/--
    For composable morphism : 
    `to_matrix (ψ ⊚ φ) =   to_matrix ψ  ⬝ to_matrix φ`
-/
@[simp]lemma to_matrix_mul (φ : (X → R) →ₗ[R] (Y → R))(ψ : (Y → R) →ₗ[R] (Z → R))  : 
   to_matrix (ψ ⊚ φ) =   to_matrix ψ  ⬝ to_matrix φ := 
begin
    apply proof_strategy, erw to_matrix_to_lin,
    rw mul_to_lin, rw to_matrix_to_lin, rw to_matrix_to_lin,
end
/--
    `to_matrix (ψ + φ) =   to_matrix ψ  + to_matrix φ`
-/
@[simp]lemma to_matrix_add (φ ψ  : (X → R) →ₗ[R] (Y → R)) : 
            to_matrix (φ + ψ ) = to_matrix (φ )+ to_matrix(ψ) :=
begin 
    --change linear_equiv_matrix'.to_fun _ = _ ,
    --erw linear_equiv_matrix'.add, exact rfl,
    apply proof_strategy,
    rw to_matrix_to_lin,
    rw to_lin_add, 
    rw to_matrix_to_lin, rw to_matrix_to_lin,
end
/-! 
    For composable morphism : 
    `to_matrix (ψ ⊚ φ) =   to_matrix ψ  ⬝ to_matrix φ`
-/

@[simp]lemma to_matrix_smul (r : R) (φ : (X → R) →ₗ[R] (Y → R))  : 
   to_matrix (r •  φ) =   r •  (to_matrix φ) := 
begin
    apply proof_strategy, 
    rw to_matrix_to_lin, 
    erw is_linear_map.smul (to_lin) (r) (to_matrix (φ )),
    rw to_matrix_to_lin,
end
/-! 
    `to_matrix (0) =   0`
-/
@[simp] lemma to_matrix_zero : to_matrix (0 : (X → R) →ₗ[R] (Y → R)) = 0 :=
begin 
    apply proof_strategy, rw to_matrix_to_lin, rw to_lin_zero,
end
/-!  
    `to_matrix (1) =   1`
-/
@[simp] lemma to_matrix_one  : to_matrix (1 : (X → R) →ₗ[R] (X → R)) = 1 :=
begin 
    apply proof_strategy,
    rw to_matrix_to_lin,
    rw to_lin_one, exact rfl,
end
/-! 
    `matrix.trace X R R (to_matrix (ψ  ⊚ φ )) =  matrix.trace Y R R (to_matrix (φ ⊚ ψ ))`
-/
@[simp]lemma to_matrix_trace_comm (φ : (X → R) →ₗ[R] (Y → R))(ψ : (Y → R) →ₗ[R] (X → R)) :
matrix.trace X R R (to_matrix (ψ  ⊚ φ )) =  matrix.trace Y R R (to_matrix (φ ⊚ ψ )) := 
begin 
    rw to_matrix_mul,
    rw trace_mul_comm, rw ← to_matrix_mul,
end
/--
    `to_matrix (∑ w, φ w) = ∑ w, to_matrix (φ w)`
-/
lemma to_matrix_sum {W : Type w'} [fintype W][decidable_eq W] (φ : W → (X → R) →ₗ[R] (Y → R) ) : 
to_matrix (∑ w, φ w) = ∑ w, to_matrix (φ w) := 
begin 
    apply proof_strategy, rw to_matrix_to_lin,
    rw ←  finset.sum_hom finset.univ  to_lin, 
    congr,funext,rw to_matrix_to_lin, by apply_instance,
end
/-!
    `trace  (∑ w, φ w) = ∑ w, trace (φ w)`
-/
lemma sum_trace {W : Type w'} [fintype W][decidable_eq W] (φ : W → (matrix X X R )) : 
matrix.trace X R R (∑ w, φ w) = ∑ w, matrix.trace X R R (φ w) :=
begin 
    rw ← finset.sum_hom finset.univ (matrix.trace X R R),
end
/--
    `trace (to_matrix ( ∑ w, φ w ) ) =  ∑ w, trace (to_matrix (  φ w ) )`
-/
lemma to_matrix_sum_trace {W : Type w'} [fintype W][decidable_eq W] (φ : W → (X → R) →ₗ[R] (X → R) ) : 
matrix.trace X R R (to_matrix ( ∑ w, φ w ) ) =  ∑ w, matrix.trace X R R (to_matrix (  φ w ) ) := 
eq.trans  (congr_arg (matrix.trace X R R) (to_matrix_sum φ)) (sum_trace (λ w, to_matrix (φ w)))

/--  
    For `φ : W → matrix Y X R ` we have  `(∑ s, φ s )  y x = ∑ s, (φ s y x)`
-/
lemma sum_apply_mat {W : Type w'} [fintype W][decidable_eq W] (φ : W → matrix Y X R )(x : X) (y : Y) : (∑ s, φ s )  y x = ∑ s, (φ s y x) := 
begin 
    rw finset.sum_apply, rw finset.sum_apply,
end
/--
    `trace  M = ∑ i, M i i`
-/
lemma trace_value (M : matrix X X R) : matrix.trace X R R M = ∑ i, M i i := rfl


lemma homo_eq_diag (f : (X → R) →ₗ[R] (X → R))(t :R) (hyp : f + t • 1 = 0) :
to_matrix f = (- t) • (1 : matrix X X R ) := 
begin 
    have : f = f+ t• 1+ (-t) • 1,
        simp,
    rw this, rw hyp,rw zero_add, rw to_matrix_smul, rw to_matrix_one,
end