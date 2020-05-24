import linear_algebra.nonsingular_inverse 
import linear_algebra.matrix
import linear_algebra.finite_dimensional
import basic_definitions.equiv
import ring_theory.ideals
import Tools.tools
import ring_theory.ideal_operations
set_option pp.generalized_field_notation false
universes u v
variables variables {X : Type u} [fintype X] [decidable_eq X] {R : Type v}[field R]
open matrix linear_map
open_locale matrix
lemma matrix.smul_zero (r : R) : r • (0 : matrix X X R) = 0 := 
begin 
    ext, rw smul_val, rw zero_val, rw mul_zero,
end
lemma matrix.zero_smul ( M : matrix X X R) : (0  : R) • M = 0 := 
begin 
    ext,rw smul_val, rw zero_mul, exact rfl,
end
/--
Change to non empty or something like that 
-/
lemma terere  (M : matrix X X R) (N : matrix X X R) (x : X) : mul_vec M (λ i, N i x) = λ i, (M ⬝ N) i x := rfl
lemma kernel_nonempty (M : matrix X X R) (x : X) : det M = 0 → ∃ v : X → R, mul_vec  M v  = 0 := 
begin 
    intros, 
    let adj := adjugate M,
    use λ i,adj i x,
    let f := mul_adjugate M, rw a at f, erw matrix.zero_smul 1 at f,
    rw terere,funext,  rw f, exact rfl, assumption,
end 
/--
    A revoir un peu, ce n'est pas bon du toiut j'ai oublié le vecteur nul ! 
-/
lemma kernel_nonempty_lin (φ : (X → R) →ₗ[R] (X → R))(x : X) :det (linear_map.to_matrix φ)  = 0 →  (∃ v : X → R, φ v = 0) :=
begin 
    intros, rcases kernel_nonempty (linear_map.to_matrix φ) x a with ⟨ ζ,hyp ⟩,use ζ,
    have : φ = matrix.to_lin (linear_map.to_matrix φ), 
        rw to_matrix_to_lin,
        rw this,
        rw to_lin_apply (to_matrix φ ) ζ , 
        rw hyp,
end
variables {Y : Type u} [fintype Y] [decidable_eq Y]
def is_injective (M : matrix X Y R) := (∀ v : Y → R, mul_vec M v = 0 → v = 0 )

lemma is_injective_to_lin_ker (M : matrix X X R) (hyp : is_injective M) : ker (to_lin M) = ⊥ := 
begin 
    rw eq_bot_iff, rw submodule.le_def',
     intros, rw submodule.mem_bot,
    rw mem_ker at H, rw to_lin_apply at H, exact hyp x H,
end
#check X
/-!
    Le theorem fondamentale du rang ! 
-/
open equiv_morphism
open_locale classical
theorem exist_ker_not_trivial (φ : (X→ R) →ₗ[R] (X → R)) : det  (linear_map.to_matrix φ) = 0 → (∃ v : X → R, (v ≠  0) ∧  (φ v = 0)) := begin 
    intros, by_contradiction,
    push_neg at a_1,
    have : ker φ = ⊥, 
        rw eq_bot_iff,
        rw submodule.le_def',
        intros,
        erw submodule.mem_bot,specialize a_1 x,
        cases a_1, exact a_1, rw mem_ker at *, trivial ,
        have range : range φ  = ⊤,
             apply linear_map.ker_eq_bot_iff_range_eq_top.mp, exact this,
        by apply_instance,
        let gk := equiv_morphism.ker_im_equiv'' φ ⟨this, range ⟩,
        have fact1 : φ = linear_equiv.to_linear_map gk,
            rw equiv_morphism.ker_im_equiv_ext'',
        let φ' := linear_equiv.to_linear_map gk.symm,
        have : φ ⊚ φ'  =  linear_map.id,
          rw fact1, rw linear_equiv_compo_id,
        have Fact2:  (linear_map.to_matrix φ) ⬝ (linear_map.to_matrix φ') = 1,
            rw ← to_matrix_mul, rw this, erw to_matrix_one,
        have : (det (linear_map.to_matrix φ)) * (det (linear_map.to_matrix φ'))=1,
            rw ← det_mul,
            rw Fact2, rw det_one,
        erw [a, zero_mul] at this,
        exact zero_ne_one this,
end

