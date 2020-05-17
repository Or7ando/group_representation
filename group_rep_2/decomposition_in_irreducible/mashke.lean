import Reynold_operator.reynold
import basic_definitions.kernel_range
import Tools.tools
open Reynold stability morphism_module linear_map
open_locale big_operators
universes  u v w w'
variables   {G : Type u} [group G][fintype G] 
            {R : Type v}[comm_ring R]  
            {M : Type w}[add_comm_group M] [module R M]  
            ( ρ : group_representation G R M) 
            (W : submodule  R M)
            [stable_submodule ρ  W]
@[simp]lemma fact_minus_one (p : M→ₗ[R]M )(hyp : is_projector p)(x : M) : p (p x) = p x := 
begin
     change (has_mul.mul p  p) x = p x,
     unfold is_projector at hyp,
     rw hyp,
end 
lemma fact0 (g : G) (x : M) : ρ g ((ρ g⁻¹) x) = x := 
begin 
    change ((ρ g) * (ρ g⁻¹ )) x = x,
    erw ← ρ.map_mul,
    erw mul_inv_self,
    erw ρ.map_one, exact rfl,  
end
/--
    Ici les lemmes sont a mettre dans Reynold opérator ! 
-/
lemma fact1 (p : M→ₗ[R]M )(hyp : is_projector p) (g : G) : is_projector (mixte_conj ρ ρ p g) :=
begin 
    unfold is_projector at *, -- change _ ⊚ _ = _,
    unfold mixte_conj,
    change _ ⊚ (p * (ρ g ⊚ ρ g⁻¹) * p) ⊚ _ = _,
    rw ← map_comp, rw mul_inv_self, rw ρ.map_one, rw mul_one,rw hyp,
end 
lemma range_mixte_conj (p : M→ₗ[R]M )(g : G) : 
    range (mixte_conj ρ ρ p g) =  submodule.map (ρ g⁻¹ ) (range p) :=
 begin 
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
lemma range_grall(hyp : stability.stable_submodule ρ  W) ( g : G) : submodule.map (ρ g)  W = W  := begin 
    apply le_antisymm,
        {rw submodule.le_def' ,intros x, intro hyp',  rcases hyp' with  ⟨y, ⟨ hyp_y, hyp_y_2⟩   ⟩,
         rw ← hyp_y_2, apply stab, exact hyp_y,},
        {rw submodule.le_def',intros x,  intro certifa, rw submodule.mem_map, 
        use (ρ g⁻¹ ) x, split,
            {
                apply stab, by assumption,
            },
            {
                erw fact0},}
    
end
theorem pre_mask (hyp : stability.stable_submodule ρ  W) (Hyp : has_projector W) (a : R )  (inv : a * (fintype.card G) = 1 ) : 
∃ F : ρ ⟶ ρ,is_projector F.ℓ ∧  linear_map.range (F.ℓ) = W   :=  
begin 
    rcases Hyp with ⟨p,hyp_p⟩,
    use a • (ℛ ρ ρ  p), 
    rw coe_smul, --- amélioration de la class homothetic 
    erw reynold_ext,
    apply   @sum_proj R _  M _ _  G _ W a _,
    apply fact1, exact  hyp_p.1,
    intros g, rw range_mixte_conj,rw hyp_p.2,rw range_grall, assumption,
    assumption, 
end 