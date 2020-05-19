import linear_algebra.basic
notation f ` ⊚ `:80 g:80 :=  linear_map.comp f g
set_option pp.generalized_field_notation false
universes u v v'
variables {R : Type u}[comm_ring R]{M : Type v}[add_comm_group M] [module R M ](f : M →ₗ[R]M) 
open linear_map
open_locale big_operators

def  is_projector (p : M →ₗ[R] M) := p * p = p

lemma is_projector_iff {p : M →ₗ[R]M} :  is_projector p ↔ p * p = p := iff.rfl 
/--
    if `p² = p` then `(1-p)² = 1 - p - p +p² = ... = 1-p`
-/

lemma Complementary (p : M →ₗ[R]M) (hyp : is_projector p) : is_projector (id - p) := 
begin
    change linear_map.id - p with 1 -p,
    have R : ( 1- p) * (1 -p) = 1 - p -(p - p * p),
        exact mul_sub (1 - p) 1 p,
    unfold is_projector,
    rw R,
    rw is_projector_iff.mp hyp,
    simp,
end
variables (p : M→ₗ[R]M)

lemma Projector_apply (x : M) :  p ∘ p =  ⇑(p * p) := rfl   

/--
        Helper : cause i use element. 
-/
lemma image_in_range (x : M) : p x ∈ range p :=  mem_range.mpr  ⟨x , rfl ⟩  



lemma ker_eq_im_comp (hyp : is_projector p) : range p = ker (id-p) := 
begin
    apply submodule.ext,intros x,split,rintros ⟨y,hyp  ⟩, rw mem_ker, change x- p x = 0, rw ← hyp.2, 
    change (p - p * p) y = 0, rw is_projector_iff.mp, rw sub_self, exact rfl,assumption,
    intros hyp, rw mem_ker at hyp, change x-p x = 0 at hyp, rw mem_range, use x,  
    have R : x - p x + p x = p x,
        rw hyp_1,
        rw zero_add,
    rw ← R,simp,
  end


def has_projector (P : submodule R M) := 
        ∃ p : M →ₗ[R]M, is_projector p ∧ linear_map.range (p : M→ₗ[R]M)  = P


lemma projector_ker (p : M →ₗ[R]M) (hyp : is_projector p) : ∀ m : M, p m ∈ ker (id - p) :=
begin 
    rw ← ker_eq_im_comp, exact image_in_range p,assumption,
end 
lemma  calcul : linear_map.id - (id - p) = p := begin exact sub_sub_self id p, end

lemma projector_range (p : M →ₗ[R]M) (hyp : is_projector p) : ∀ m : M, m - p m ∈ ker (p) := 
begin 
    let H := projector_ker (id-p) (Complementary p hyp),    
    -- let H := specialize (proj_ker (id - p)) (Complementary p hyp)  -- unknown identifier 'specialize'
    rw calcul at H,
    exact H,
end 
/--
   `is_projector p` then `∀ m ∈ M,  ∃ m_im ∈ range p, ∃ m_ker ∈ ker p`
    s.t `m = m_ker+ m_im`
-/
lemma projector_decomposition_existence (p : M →ₗ[R]M) (hyp : is_projector p) : 
    ∀ m : M,∃ m_im ∈ range p, ∃ m_ker ∈ ker p, m = m_ker+ m_im  :=
 begin 
    intros m,
    use p m,
    split, 
        {apply image_in_range},
        {use m - p m,split,
            {apply projector_range p hyp},
            {exact eq_add_of_sub_eq rfl}},
end 
lemma projector_decomposition_unicity (hyp : is_projector p) : (range p)  ⊓ (ker p)= ⊥ :=  begin 
    rw eq_bot_iff,
    rw submodule.le_def', intros x, rw submodule.mem_bot, intros, 
    rw submodule.mem_inf at H,
    rcases H with ⟨  IM, KER ⟩ ,
    rw mem_ker at KER, rw mem_range at IM, rcases IM with ⟨ y,hyp_y⟩ ,
    rw ← hyp_y at KER, change (p * p) y = 0 at KER, rw is_projector_iff.mp at KER, rw hyp_y at KER, 
assumption, assumption, 
end


lemma projector.mem_range (x : M)(hyp : is_projector p) : x ∈ range p ↔  p x = x := 
begin 
    split, 
        intro hyp, 
        rw mem_range at hyp, rcases hyp with ⟨y,hyp_y ⟩, rw ← hyp_y, change p( p y) with (p *p) y, rw (is_projector_iff.mp hyp),
        intro hyp, rw ← hyp,
        apply image_in_range, 
end 


lemma projector_im_eq (p q : M→ₗ[R] M) (hyp_p : is_projector p) (hyp_q : is_projector q) : 
            range  p =  range q ↔  ( p * q = q) ∧  (q * p = p) := begin  
        split, 
        intro hyp,
            split,
                {ext,rw mul_app, rw ← projector.mem_range, rw hyp,refine image_in_range q _, assumption},
                {ext, rw mul_app,rw ← projector.mem_range,rw ← hyp,refine image_in_range p _, assumption},
            intro, 
            apply submodule.ext,
            intro x, split,
                {intro,rw ←  a.2 at a_1,rw mem_range at *,rcases a_1,use p a_1_w, exact a_1_h,},
                {intro,rw ←  a.1 at a_1,rw mem_range at *,rcases a_1,use q a_1_w, exact a_1_h,},
end
/--
   if  `∀ x : range p, p x = x `  then  `is_projector p`
-/
theorem is_projector_range_id (p : M→ₗ[R]M) : (∀ x : range p, p x = x ) → is_projector p := begin 
    intro hyp, apply is_projector_iff.mpr,
    ext,rw mul_app,
    exact hyp ⟨p x , image_in_range p x ⟩, 
end
lemma range_le_submodule_iff (p : M→ₗ[R]M) (W : submodule R M) : range p ≤ W ↔  ∀ x : M,  p x ∈ W :=
begin 
    split, intros hyp, intro x, let R := image_in_range p x,
    rw submodule.le_def' at hyp,
    exact hyp (p x) R,
    intro,
    rw submodule.le_def', intro x, intro hyp_range, rw mem_range at hyp_range, rcases hyp_range, 
    rw ← hyp_range_h, exact a hyp_range_w,
end
/--
    if `range p ≤ W ∧ ∀ w ∈ W, p w = w`  then  `is_projector p ∧ range p = W` 
-/
theorem is_projector_range_le_and_id (p : M→ₗ[R]M) (W : submodule R M) : (range p ≤ W ∧ ∀ w ∈ W, p w = w) → (is_projector p
∧ range p = W) := 
begin 
    intros hyp,
    split, 
        apply is_projector_range_id,
            intro y, 
                apply hyp.2 y, -- ici un peu long 
        rw submodule.le_def' at hyp,
        apply hyp.1 y,
        exact y.property,
        apply le_antisymm , 
            exact hyp.1,
            rintros w, 
            intro hyp_w,
            change w ∈ range p,
            change w ∈ W at hyp_w,
            rw mem_range,
            use w,
            rw hyp.2,assumption,
end




lemma sum_range (X :Type v')[fintype X](φ : X → (M →ₗ[R] M))(W : submodule R M) : 
    (∀ x : X, range (φ x) ≤ W)  → linear_map.range (finset.sum finset.univ φ ) ≤ W :=  
begin
    intros hyp,
    rw submodule.le_def',
    intros m,
    intros, rw linear_map.mem_range at H,
    rcases H with ⟨y,hyp_y ⟩,
    rw ← hyp_y,
    rw linear_map.sum_apply,  
    apply submodule.sum_mem,  
    intros c,  intros,
    let hyp := hyp c, rw submodule.le_def' at hyp,
    apply hyp, exact image_in_range (φ c) y, 
end


lemma range_smulll (a : R)(b : R) (hyp : a * b = 1)  : range (a • p) = range p := 
begin 
    apply le_antisymm,
    rw submodule.le_def',
    intros x, intros hyp, rw linear_map.mem_range at *, rcases hyp with ⟨ y, hyp_y ⟩,
    use  a • y,
    rw linear_map.map_smul,  exact hyp_y,
    rw submodule.le_def',
     intros x, intros hyp, rw linear_map.mem_range at *, rcases hyp with ⟨y, hyp_y  ⟩,
     use b • y,
     rw linear_map.map_smul, erw ← mul_smul, rw mul_comm, rw hyp, rw one_smul, assumption, 
end 



lemma sum_proj (X  : Type v')[fintype X](W  : submodule R M)(a : R) 
(inve : a * (((fintype.card X) : ℤ)  : R) = 1) (φ : X → (M →ₗ[R]M)) (hyp : ∀ x : X, is_projector (φ x)) 
(hyp_2 : ∀ x : X, range (φ x) = W) :
  is_projector ( a • (finset.sum finset.univ φ)) ∧ range ( a • (finset.sum finset.univ φ)) = W   := 
begin
    apply is_projector_range_le_and_id,
    split, 
    rw range_smulll,
    swap, use inve,
    apply sum_range,
    intros x,
    rw hyp_2 x,
    rw submodule.le_def,
    intros x, intros hyp',
    change a • _ =x,
    rw linear_map.sum_apply,
    have R' : (λ d, φ d x) = (λ d, x),
        funext,
        rw ← projector.mem_range (φ d) x (hyp d),
        rw hyp_2 d, 
        assumption,
    rw R',
    rw finset.sum_const,
    change a • (( fintype.card X) • x) = x,
    rw   semimodule.smul_eq_smul R,
    rw ← mul_smul,
    erw inve, rw one_smul,
end  