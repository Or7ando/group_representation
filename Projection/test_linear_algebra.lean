import tactic.ring_exp
import algebra.module 
import linear_algebra.basic
--infix  ` * `     := linear_map.comp 
namespace Tools.module
universes u v v'

/-!
#   Goal :  explain how to deal with map between module :  for baby user ! 
*          
*   Linear algebra is one of the first abstract theory seen at school. This tutorial try to answers to 
*   the question : can i make my baby exercice using lean ? 
*   Here we deal with `R-module`  and not with `k-vector space` there is nothing different 
*   at the beginning. 
*   This file try to explain the basic command to play with `linear_map`  `range` `kernel`. 
*   We also study a special classe of linear endomorphism `Projector` i.e 
*   endomorphism ` p : M →ₗ[R] M` satisfying  the relation `p * p = p`. 
*   This classes is important to deal with decomposition a module into  `a direct sum`.         
-/
variables {R : Type u}[comm_ring R]{M : Type v}[add_comm_group M] [module R M ](f : M →ₗ[R]M) 
example (n : ℕ) (a : R)(hyp :  a * n = 1)(x : M) : a • ((n) •  x) = x := begin 
    have R : n • x = (n : R) • x,
        exact semimodule.smul_eq_smul R n x,
    rw R,
    rw ← mul_smul,
    rw hyp,
    rw one_smul,
end
 open linear_map  submodule -- to write ker instead of linear_map.ker  
/--
    We start with the axiom of linear_map ! 
-/
example (x y : M) : f ( x + y) = f x + f y := map_add f x y
/--
    For example 
-/
example ( x y : M) :  f ( x + y) =  f y + f x := begin 
    rw map_add f ,           
    rw add_comm,        --- the addition in a module is commutative `[add_comm_group M]` 
end
/--
*     The multiplication of a scalar by a vector is denoted by `•` and name `smul` ! 
-/
example (r  : R )(x : M) : f (r • x ) =  r • f( x) := f.map_smul r x
/--
    We give the definition of `ker f`. The standant definition is the subset 
    `ker f := {x ∈ M | f x = 0}` and proof that is a submodule of `M`. In 
    mathlib the definition is not this.   
-/
example : ker f = comap f ⊥ := rfl 
/--
    `rfl` mean that is the `mathlib definition`. We see that it's construct with a function 
    `linear_map.comap` and with a notation `⊥`. We explain this. 
    1. `⊥` refer to the bottom element of the set of `submodule` of `M` that mean `⊥ = {0}` 
    2. `comap f ` is the inverse inmage `f⁻¹`. 
    So `comap f ⊥ := f⁻¹ {0}` this is the set of element of ` x ∈ M` s.t `f x = 0`      
-/
example (x : M) : x ∈ (⊥ : submodule R M)  ↔  x = 0 := mem_bot _ 
/--
    the classical definition of comap ` x ∈ f⁻¹ p ↔ f x ∈ p` 
-/
example (x : M)(p : submodule R M) : x ∈ comap f p ↔ f x ∈ p := mem_comap 
/--
    the standart for `ker f`
-/
example (x : M) : x ∈ ker f ↔ f x = 0 := begin 
    unfold ker, 
    rw mem_comap, 
    rw mem_bot,
end
/--
*   This command is in mathlib ! 
-/
example (x : M ) : x ∈ ker f ↔ f x = 0 := mem_ker  
variables (g : M→ₗ[R]M)
/--
*  a little exercice. I give two proof. The first use property of comap and is `ez` !   
-/ 
lemma exercice (x : M) : x ∈ ker (g * f)  ↔  f x ∈ ker g := begin 
    unfold ker,  
    erw comap_comp,  --- the erw is important here to change linear map comp and  `*` 
    rw mem_comap, 
end
/--
* In the second, i split in detail ! The see an important fact : if you don't use the definition 
    thing are harder ! 
-/
lemma exercice' (x : M) : x ∈ ker (g * f)  ↔  f x ∈ ker g := begin 
    split, intros hyp,
    rw mem_ker at hyp, 
    rw mem_ker,  
    exact hyp,  -- here : important to look the tatic state ' hyp :  (g * f ) x = 0 and the goal in not the same ! 
                --  But by definition (g * f )x = g (f x) so it's good ,  you can  'rw mul_app at hyp,'
    intros hyp, 
    rw mem_ker at hyp ⊢,   -- rewrite at hyp and at the goal ! 
    exact hyp,
    end
lemma Ker_zero : ker (0 : M→ₗ[R]M) = ⊤ := 
begin 
    rw eq_top_iff', 
        intros x,
        exact mem_ker.mpr rfl,
end
/--
* this function is yet in mathlib !
<-/
example  : ker f = ⊤ ↔ f  = 0 := ker_eq_top  
/--
* Now we deal with `range f`. The definition is `map f ⊤`.  
-/
example : range f = map f ⊤ := rfl 
/--
    clasical definition 
*  This command his in mathlib has `mem_range` -/

example : ker (0 : M→ₗ[R]M) = ⊤ := ker_zero
/--
* Another mathlib function : `ker_eq_top`  
*    We `redo a proof` ! 
-/
lemma  ker_eq_top' : f  =  0 ↔ ker f = ⊤  := 
begin 
    split,   -- separation ↔ 
        -- first part is the previous lemma   
        {intros hyp, rw hyp, exact ker_zero},
        intros hyp,
            rw eq_top_iff' at hyp, ext, change f x  = 0, rw ← mem_ker,
            exact hyp x,
end 

lemma ker_eq_top'' : (∀ x : M, f x = 0) ↔ ker f = ⊤  := begin 
    split, intros,
    rw  ker_eq_top, ext, exact a  x,
    intros, rw  ker_eq_top at a, change f x = 0, rw a, exact rfl,
end
/-!
*       We see that it complicated for a triviality. 
*       because we don't use realy the definition 
-/
example : ker f = comap f ⊥  := rfl
example : range f  = map f ⊤ := rfl 
/-! 
*       We have to deal with this definition to make stuff simpler
-/
lemma ker_eq_top  : range f = ⊥  ↔  ker f = ⊤ := begin 
    rw eq_top_iff, 
    rw eq_bot_iff, -- unfold ker range,
    exact map_le_iff_le_comap,
end


lemma range_bot_iff {R : Type u} [ comm_ring R]{M : Type v}[add_comm_group M][module R M] (f: M →ₗ[R] M) 
: (f = 0) ↔   linear_map.range f = ⊥   := 
 begin  rw eq_bot_iff, rw linear_map.range_le_bot_iff f, 
 end
lemma linear_map.range_sub_ker (R : Type u) [ comm_ring R](M : Type v)[add_comm_group M][module R M] (f g : M →ₗ[R] M) :
                f * g = 0  ↔ range g ≤ ker f :=
begin
    rw range_bot_iff (f * g),
    rw linear_map.le_ker_iff_map, 
    erw ← submodule.map_comp, exact iff.rfl,
end
end Tools.module

universes u v v'
variables {R : Type u}[comm_ring R]{M : Type v}[add_comm_group M] [module R M ]
open linear_map

def  is_projector (p : M →ₗ[R] M) := p * p = p

lemma is_projector_ext {p : M →ₗ[R]M} (hyp : is_projector p) : p * p = p := 
begin unfold is_projector at hyp,exact hyp, end
/--
    if `p² = p` then `(1-p)² = 1 - p - p +p² = ... = 1-p`
-/
lemma Complementary (p : M →ₗ[R]M) (hyp : is_projector p) : is_projector (id - p) := begin
    change linear_map.id - p with 1 -p,
    have R : ( 1- p) * (1 -p) = 1 - p -(p - p * p),
        exact mul_sub (1 - p) 1 p,
    unfold is_projector,
    rw R,
    rw is_projector_ext hyp,
    simp,
end
variables (p : M→ₗ[R]M)

lemma Projector_apply (x : M) :  p ∘ p =  ⇑(p * p) := rfl   

lemma image_in_range (x : M) : p x ∈ range p := by apply mem_range.mpr; use x


lemma ker_eq_im_comp (hyp : is_projector p) : range p = ker (id-p) := begin
    apply submodule.ext,intros x,split,rintros ⟨y,hyp  ⟩, rw mem_ker, change x- p x = 0, rw ← hyp.2, 
    change (p - p * p) y = 0, rw is_projector_ext, rw sub_self, exact rfl,assumption,
    intros hyp, rw mem_ker at hyp, change x-p x = 0 at hyp, rw mem_range, use x,  
    have R : x - p x + p x = p x,
        rw hyp_1,
        rw zero_add,
    rw ← R,simp,
  end


def has_projector (P : submodule R M) := 
        ∃ p : M →ₗ[R]M, is_projector p ∧ linear_map.range (p : M→ₗ[R]M)  = P


lemma proj_ker (p : M →ₗ[R]M) (hyp : is_projector p) : ∀ m : M, p m ∈ ker (id - p) := 
begin 
    rw ← ker_eq_im_comp, exact image_in_range p,assumption,
end 
lemma  calcul : linear_map.id - (id - p) = p := begin exact sub_sub_self id p, end

lemma proj_im(p : M →ₗ[R]M) (hyp : is_projector p) : ∀ m : M, m - p m ∈ ker (p) := 
begin 
    let H := proj_ker (id-p) (Complementary p hyp),    
    -- let H := specialize (proj_ker (id - p)) (Complementary p hyp)  -- unknown identifier 'specialize'
    rw calcul at H,
    exact H,
end 
lemma projector_decomp (p : M →ₗ[R]M) (hyp : is_projector p) : 
    ∀ m : M,∃ m_im ∈ range p, ∃ m_ker ∈ ker p, m = m_ker+ m_im  := begin 
        intros m,
        use p m,
        split, refine image_in_range _ m ,
        use m - p m,
        split,
        apply proj_im,
        assumption,simp,
     end 
lemma Unicity (hyp : is_projector p) : (range p)  ⊓ (ker p)= ⊥ :=  begin 
    rw eq_bot_iff,
    rw submodule.le_def', intros x, rw submodule.mem_bot, intros, 
    rw submodule.mem_inf at H,
    rcases H with ⟨  IM, KER ⟩ ,
    rw mem_ker at KER, rw mem_range at IM, rcases IM with ⟨ y,hyp_y⟩ ,
    rw ← hyp_y at KER, change (p * p) y = 0 at KER, rw is_projector_ext at KER, rw hyp_y at KER, 
assumption, assumption, 
end
lemma projector.mem_range (x : M)(hyp : is_projector p) : x ∈ range p ↔  p x = x := begin 
    split, 
        intro hyp, rw mem_range at hyp, rcases hyp with ⟨y,hyp_y ⟩,
        rw ← hyp_y,
        change p( p y) with (p *p) y,
        rw (is_projector_ext hyp),
        intro hyp,
        rw ← hyp,
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

theorem projector.caract_image (p : M→ₗ[R]M) : (∀ x : range p, p x = x ) → is_projector p := begin 
    intro hyp, unfold is_projector,
    ext,rw mul_app,
    exact hyp ⟨p x,image_in_range p x ⟩, 
end
lemma range_le_submodule (p : M→ₗ[R]M) (W : submodule R M) : range p ≤ W ↔  ∀ x : M,  p x ∈ W := begin 
    split, intros hyp, intro x, let R := image_in_range p x,
    rw submodule.le_def' at hyp,
    exact hyp (p x) R,
    intro,
    rw submodule.le_def', intro x, intro hyp_range, rw mem_range at hyp_range, rcases hyp_range, 
    rw ← hyp_range_h, exact a hyp_range_w,
end
theorem projector.caract_image' (p : M→ₗ[R]M) (W : submodule R M) : (range p ≤ W ∧ ∀ w ∈ W, p w = w) → (is_projector p
∧ range p = W) := 
begin 
    intros hyp,
    split, 
        apply projector.caract_image,
        intro y, 
        apply hyp.2 y,
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
lemma projector.right_mul (p f : M →ₗ[R] M) [is_projector p] : 
    p * f = f  ↔ ∀ x : M, (x ∈ range f →  p x = x) := begin 
    split, intro hyp, intro x, rw mem_range, rintros ⟨a,b⟩, 
    rw ← b, change (p * f) a = f a,
    rw hyp,
    intro hyp,
    ext, exact hyp _  (image_in_range f x), 
end


variables (g : M ≃ₗ[R]M)
example (N : submodule R M) : N ≤ ⊤ := le_top 
example  (N N' : submodule R M) : (N ≤ N') → (N' ≤ N) → N = N'  := le_antisymm 

open submodule
lemma submodule.le_inf (W N N' : submodule R M) : W ≤ N ⊓ N' ↔  (W ≤ N ∧ W ≤ N') := le_inf_iff 
lemma test' (p f : M →ₗ[R] M) : map f (ker (p * f)) = range f ⊓ ker p := begin 
    apply le_antisymm, 
        rw le_inf_iff, 
            split, 
                {apply map_mono , exact le_top},
                {rw linear_map.le_ker_iff_map,
                erw ← map_comp,
                rw ← linear_map.le_ker_iff_map,
                exact le_refl _},
            intros x, intros hyp, rcases hyp, erw mem_map, 
            change x ∈ range f at hyp_left,
            rw mem_range at hyp_left, rcases hyp_left with ⟨y, hyp_y⟩ ,use y, split, swap, assumption,
            rw mem_ker, change  x ∈ ker p at hyp_right, change  p( f y) = 0, rw hyp_y, exact mem_ker.mp hyp_right,
end 
lemma test'' (p f : M →ₗ[R] M) : map f (ker (p * f)) = range f ⊓ ker p := begin 
    apply le_antisymm, 
         rw le_inf_iff,
            split,  apply map_le_range,
                rw map_le_iff_le_comap,  
                {   erw comap_comp, refine le_refl _,},
                rw le_def',
                intros x, intros hyp, rcases hyp, rw mem_map, 
                erw mem_range at hyp_left, rcases hyp_left with ⟨y, hyp_y⟩ ,use y, split, swap, assumption,
                rw mem_ker, change  x ∈ ker p at hyp_right, change  p( f y) = 0, rw hyp_y, exact mem_ker.mp hyp_right,
end 

open finset

lemma sum.range (X :Type v')[fintype X](φ : X → (M →ₗ[R] M))(W : submodule R M) : 
    (∀ x : X, range (φ x) ≤ W)  → linear_map.range (finset.sum finset.univ φ ) ≤ W :=  
begin
    intros hyp,
    rw le_def',
    intros m,
    intros, rw linear_map.mem_range at H,
    rcases H with ⟨y,hyp_y ⟩,
    rw ← hyp_y,
    rw linear_map.sum_apply,  
    apply sum_mem,  
    intros c,  intros,
    let hyp := hyp c, rw le_def' at hyp,
    apply hyp, exact image_in_range (φ c) y, 
end


lemma range_smulll (a : R)(b : R) (hyp : a * b = 1)  : range (a • p) = range p := begin 
    apply le_antisymm,
    rw le_def',
    intros x, intros hyp, rw linear_map.mem_range at *, rcases hyp with ⟨ y, hyp_y ⟩,
    use  a • y,
    rw linear_map.map_smul,  exact hyp_y,
    rw le_def',
     intros x, intros hyp, rw linear_map.mem_range at *, rcases hyp with ⟨y, hyp_y  ⟩,
     use b • y,
     rw linear_map.map_smul, erw ← mul_smul, rw mul_comm, rw hyp, rw one_smul, assumption, 
end 
lemma sum_proj (X  : Type v')[fintype X](W  : submodule R M)(a : R) 
(inve : a * (((fintype.card X) : ℤ)  : R) = 1) (φ : X → (M →ₗ[R]M)) (hyp : ∀ x : X, is_projector (φ x)) 
(hyp_2 : ∀ x : X, range (φ x) = W) :
  is_projector ( a • (finset.sum finset.univ φ)) ∧ range ( a • (finset.sum finset.univ φ)) = W   := 
begin
    apply projector.caract_image',
    split, 
    rw range_smulll,
    swap, use inve,
    apply sum.range,
    intros x,
    rw hyp_2 x,
    rw le_def,
    intros x, intros hyp',
    change a • _ =x,
    rw linear_map.sum_apply,
    have R' : (λ d, φ d x) = (λ d, x),
        funext,
        rw ← projector.mem_range (φ d) x (hyp d),
        rw hyp_2 d, 
        assumption,
    rw R',
    rw sum_const,
    change a • (( fintype.card X) • x) = x,
    rw   semimodule.smul_eq_smul R,
    rw ← mul_smul,
    erw inve, rw one_smul,
end  

/--
 from : http://desaintar.free.fr/exos/exos_ev.pdf
-/
lemma exercice_25 : ker (p ) ≤ ker (p * p) := begin 
    unfold ker at *,
    change  _ ≤  comap (linear_map.comp p p) _  ,
    rw comap_comp,
    apply comap_mono,
    exact bot_le,
end
lemma exercice_25_2 : range (p * p) ≤ range p := 
begin
    unfold linear_map.range at  *,
    erw map_comp,
    apply map_mono,
    exact le_top,
end
lemma exercice_26' : ker (p *p) = ker p ↔ range p ⊓ ker (p) = ⊥ := begin 
           rw ←  map_comap_eq,rw eq_bot_iff,
           rw map_le_iff_le_comap, unfold ker,
           rw ← comap_comp,
           split,
           intros, rw ← a, exact le_refl _,
           intros, apply le_antisymm, exact a, 
           erw comap_comp, apply comap_mono, exact bot_le,           
end 


lemma exercice_33 (p q : M →ₗ[R]M)(hyp_p : is_projector p)(hyp_q : is_projector q) (comm : p * q = q * p) :  
    is_projector (p*q) := 
begin 
    unfold is_projector at  *,
    rw mul_assoc, rw comm, rw ← mul_assoc q q p, rw hyp_q, rw ← comm, rw ← mul_assoc, rw hyp_p,
end
