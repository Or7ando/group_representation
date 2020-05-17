import algebra.module
import linear_algebra.basic
--infix  ` * `     := linear_map.comp
universes u v
variables {R : Type u}[comm_ring R]{M : Type v}[add_comm_group M] [module R M ]
open linear_map
def  Projector (p : M →ₗ[R] M) := p * p = p

/--
    if `p² = p` then `(1-p)² = 1 - p - p +p² = ... = 1-p`
-/
lemma Complementary (p : M →ₗ[R]M) [Projector p] : Projector (1 - p) := begin
    unfold Projector,
    rw mul_sub_left_distrib,
    iterate 2 { rw mul_sub_right_distrib,rw mul_one},
    unfold Projector at *,
    rw _inst_4,
    rw one_mul,
    simp,
end
variables (p : M→ₗ[R]M)
lemma ker_eq_im_complementary (hyp : Projector p ) : range p = ker (1-p) := begin
    apply submodule.ext,
    intros x,
    split,
        intros x_in_range,
        rw mem_range at x_in_range,
        rcases x_in_range with ⟨y,hyp_y⟩,
        rw mem_ker,
        rw ← hyp_y,
        simp,
        rw ← function.comp_apply ⇑p,
        unfold Projector at hyp,
        erw hyp,       --- here  do you have an idea to make the coersion of the  composition easy ?
end