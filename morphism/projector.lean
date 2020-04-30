import morphism.Reynold_operator
import sub_module
import homothetic
import Projection.test_linear_algebra
open Reynold
universes  u v w w'
#eval 1+5  
#check ℛ 
variables {G : Type u} [group G][fintype G] {R : Type v}[comm_ring R]  
variables  {M : Type w}[add_comm_group M] [module R M]  ( ρ : group_representation G R M) 
(W : submodule  R M)(hyp : stability.stable_submodule ρ  W)
#check ℛ ρ 
lemma fact_minus_one (p : M→ₗ[R]M )(hyp : is_projector p)(x : M) : p (p x) = p x := 
begin
     change (has_mul.mul p  p) x = p x,
     unfold is_projector at hyp,
     rw hyp,
end 
lemma fact0 (g : G) (x : M) : ρ g ((ρ g⁻¹) x) = x := begin 
    change ((ρ g) * (ρ g⁻¹ )) x = x,
    erw ← ρ.map_mul,
    erw mul_inv_self,
    erw ρ.map_one, exact rfl,  
end
lemma fact1 (p : M→ₗ[R]M )(hyp : is_projector p) (g : G) : is_projector (mixte_conj ρ ρ p g) :=
begin
    unfold is_projector,
    unfold mixte_conj, erw mul_assoc,
    erw ← mul_assoc ↑(ρ g), erw ← mul_assoc ↑(ρ g),
    ext,simp,
    erw fact0,
    erw fact_minus_one,
    assumption,
end 
lemma range_mixte_conj (p : M→ₗ[R]M )(g : G) : linear_map.range (mixte_conj ρ ρ p g) = 
submodule.map (ρ g⁻¹  : M →ₗ[R]M ) (linear_map.range p) := begin 
    apply le_antisymm,
    unfold mixte_conj, rw submodule.le_def',
    intros x, intros hyp, rw submodule.mem_map,rw linear_map.mem_range at hyp,
    rcases hyp with ⟨y, hyp_y ⟩, 
    use p (ρ g y),split,
    exact image_in_range p _,
    rw ← hyp_y,
    exact rfl,
    rw submodule.le_def' at  *, intros x, intros hyp_x, rw linear_map.mem_range,
    rcases hyp_x with ⟨z, hyp_z⟩  , rcases hyp_z,
    erw linear_map.mem_range at hyp_z_left,
    rcases hyp_z_left with ⟨y,hyp_u⟩ , use (ρ g⁻¹ ) y,
    dunfold mixte_conj,
    rw linear_map.comp_apply, erw fact0, rw ← hyp_z_right, rw ← hyp_u, exact rfl,
end
lemma range_grall(hyp : stability.stable_submodule ρ  W) ( g : G) : submodule.map (ρ g : M →ₗ[R] M) W = W  := begin 
    apply le_antisymm,
    rw submodule.le_def' ,
    intros x, intro hyp',  rw submodule.mem_map at hyp', rcases hyp', rw ← hyp'_h.2,
    unfold stability.stable_submodule at hyp,
    let F :=  (hyp g),
    change ((ρ g) hyp'_w) ∈ W,
    exact (F ⟨ hyp'_w,hyp'_h.1⟩ ),
    rw submodule.le_def' ,
    intros x,  intro certifa, rw submodule.mem_map, 
    use (ρ g⁻¹ ) x,
    split,swap, 
    change (ρ g)( (ρ g⁻¹ ) x) = x,
    rw fact0,
    unfold stability.stable_submodule at hyp,
    let F :=  (hyp g⁻¹ ),
    exact F ⟨x,certifa⟩, 
end
theorem pre_mask (hyp : stability.stable_submodule ρ  W) (Hyp : has_projector W) (a : R )  (inv : a * (fintype.card G) = 1 ) : 
∃ F : ρ ⟶ ρ,is_projector F.ℓ ∧  linear_map.range (F.ℓ) = W   :=  
begin 
    rcases Hyp with ⟨p,hyp_p⟩,
    use a • (ℛ ρ ρ  p), 
    rw homothetic.smul_ext,
    erw reynold_ext,
    apply   @sum_proj R _  M _ _  G _ W a _,
    intros g,
    apply fact1, exact hyp_p.1,
    intros g,
    rw range_mixte_conj,rw hyp_p.2,rw range_grall, assumption,
    assumption, 
end 