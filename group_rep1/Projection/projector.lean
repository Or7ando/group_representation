import linear_algebra.basic
import data.sum
import linear_algebra.finite_dimensional
universes  u v w w' w''
set_option pp.beta true
notation `Σ` := finset.sum finset.univ 
/-!
    Goals : sudying familly of projector. 
    We start  by sudy i little projector. 
-/
namespace Projector 
open linear_map
variables {R : Type u}[comm_ring R]{M : Type v}[add_comm_group M] [module R M] 
/-!
    A linear map `p : M →ₗ[R] M)` is a projector when `p * p = p`.
-/
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
    p * f = f  ↔ ∀ x : M, (x ∈ range f →  p x = x) := 
begin 
    split, intro hyp, intro x, rw mem_range, rintros ⟨a,b⟩, 
    rw ← b, change (p * f) a = f a,
    rw hyp,
    intro hyp,
    ext, exact hyp _  (image_in_range f x), 
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
























lemma range_le_iff {p q : M →ₗ[R] M} (hyp : is_projector p)(hypq : is_projector q) : p * q = q ↔ range q ≤ range p := 
begin
    split, 
    {intros hyp, rw ← hyp, erw range_comp,apply submodule.map_mono, exact le_top,},
    {intros hyp, ext x,
        change p ( q x ) = q x,
        have r : q x ∈ range p, 
            apply hyp,
            exact image_in_range q x ,
        rw  (projector.mem_range p _ _).mp r, assumption,
        },
end 

lemma range_cap {p q : M →ₗ[R] M} (hypp : is_projector p)(hypq : is_projector q) : p * q = 0 →  range p ⊓ range q = ⊥ := 
begin
     intros hyp,rw eq_bot_iff,rw submodule.le_def',
    intros x, intro hyp, rw submodule.mem_bot,rcases hyp, erw projector.mem_range at hyp_left hyp_right,
    rw ← hyp_left, rw ← hyp_right, change ( p * q ) x = 0, rw hyp,exact rfl, assumption, assumption,
end

end Projector 











































































open Projector

def δ {X : Type w''}[decidable_eq X] (x y : X) := if  x = y then 1 else 0

structure orthogonal_familly_of_projector 
(R : Type u)[comm_ring R](M : Type v)[add_comm_group M] [module R M] (X : Type w)[fintype X][decidable_eq X]  :=
(π :  X → M →ₗ[R]M) 
(ortho : ∀ x y : X, π x * π y = (δ x y) •  π x)

namespace orthogonal_familly_of_projector
variables {R : Type u}[comm_ring R]{M : Type v}[add_comm_group M] [module R M] 
          {X : Type w}[fintype X][decidable_eq X]
          ( P : orthogonal_familly_of_projector R M X)
--instance : has_coe_to_fun(orthogonal_familly_of_projector R M X) := ⟨_, λ P, P.π ⟩ 
@[simp]lemma ortho_ite (x y : X ) : P.π x * P.π y = if x = y then P.π x else 0 := begin 
    rw P.ortho, 
    unfold δ,
    split_ifs,
    rw one_smul,
    rw zero_smul,
end
lemma single_is_projector (x : X) : is_projector (P.π x) := begin 
    unfold is_projector, erw ortho_ite, simp, 
end
def Total : M→ₗ[R]M := Σ P.π    

@[simp]lemma Fact : (λ (x : X), Σ P.π * P.π x)  = λ x, P.π  x := begin 
    funext,erw finset.sum_mul,
    simp,
end
lemma Fact1 (x : X) : P.π x * Total P = P.π x := begin 
    unfold Total,erw  finset.mul_sum, simp,
end
@[simp]theorem Total_is_projector : (Total P) * (Total P) = Total P := begin 
    unfold Total, erw finset.mul_sum, rw Fact, 
end
lemma Fact2 (x : X) :  Total P * P.π x = P.π x := begin
    unfold Total, erw finset.sum_mul,simp,
end

def Range : submodule R M :=  linear_map.range (Σ  P.π) 

@[simp] lemma Total_range : linear_map.range (Total P) = Range P := rfl

lemma single_range_sub_total_( x: X ) : linear_map.range (P.π x) ≤ Range P := begin 
    apply (range_le_iff (Total_is_projector P) (single_is_projector P x) ).mp, 
    unfold Total,erw finset.sum_mul,
    simp,
end

end orthogonal_familly_of_projector
namespace Ortho_of_familly
open orthogonal_familly_of_projector
variables {R : Type u}[comm_ring R]{M : Type v}[add_comm_group M] [module R M] 
          {X : Type w}[fintype X][decidable_eq X]
          ( P : orthogonal_familly_of_projector R M X)
variables  {Y : Type w'}[fintype Y][decidable_eq Y]  
          (Q : orthogonal_familly_of_projector R M Y)

def ortho  := ∀ x : X, ∀ y : Y,  P.π x  *  Q.π y = 0 
@[simp]lemma ortho_simp (x : X) (y : Y) : ortho P Q  → P.π  x * Q.π y = 0 := 
begin 
    intros hyp, exact hyp x y,
end
@[simp]lemma ortho_simp'  (y : Y) (hyp : ortho P Q) : (λ x : X,  P.π  x * Q.π y) = (λ x, 0) := 
begin 
    funext, exact hyp x y,
end
@[simp]lemma ortho_mul_right (hyp : ortho P Q) : (λ y :Y, (Total P) * Q.π y) = 0 := 
begin funext,
    erw finset.sum_mul,
    erw ortho_simp',
    simp, assumption,
end 
@[simp]lemma ortho_mul_total_eq_zero  : ortho P Q ↔  (Total P ) * (Total Q) = 0 := 
begin split,
    intros hyp, erw finset.mul_sum, erw (ortho_mul_right P Q hyp), simp,
    intros,unfold ortho,
    intros x y,erw ← Fact1, erw ← Fact2 Q y, rw  mul_assoc, rw ←  mul_assoc (Total P) _  _,rw a, 
    rw zero_mul, rw mul_zero,
end
/--
    Faire attention ici 
    theoreme du rang ? n = range(p) + ker(p) ...   dim (range p + range q) = dim range p + dim range q
-/
theorem ortho_iff : ortho P Q →   Range P  ⊓ Range Q = ⊥ := 
begin
    rw ortho_mul_total_eq_zero, apply range_cap, exact Total_is_projector P, 
    exact Total_is_projector Q,
    
end    
#check X ⊕ Y
namespace Test
variables 
(P1 : orthogonal_familly_of_projector R  M X)  (P2 : orthogonal_familly_of_projector R  M Y)
/--
    Faire mieux avec les complementaires ! 
-/
theorem add :   ortho P1 P2 ∧  ortho P2 P1 → orthogonal_familly_of_projector R M (X ⊕ Y) := λ certif,
 { π := sum.elim P1.π P2.π,
  ortho := 
begin 
        intros, rcases x,rcases y,unfold δ,simp,split_ifs,rw one_smul,rw zero_smul,unfold δ,simp,
        exact certif.1 x y,
        rcases y,unfold δ, simp, exact certif.2 x y,
        unfold δ, simp, -- ite smul ? 
        split_ifs,rw one_smul, rw zero_smul,
  end }
end Test 

end Ortho_of_familly
structure complete_orthogonal_familly_of_projector
(R : Type u)[comm_ring R](M : Type v)[add_comm_group M] [module R M] (X : Type w)[fintype X][decidable_eq X]
extends orthogonal_familly_of_projector R M X :=
(complete : Σ π = 1)

/-!
    vector space of finite dimension
-/
namespace vector_space
variables {K : Type u}[field K]{V : Type v}[add_comm_group V] [vector_space K V] {ι : Type w} 
[fintype ι] {b : ι → V} (h : is_basis K b)[W : submodule K V ]
#check exists_is_basis K W

#check exists_subset_is_basis
#check (@zero_ne_one K _)


example {K : Type u}[field K]{V : Type v}[add_comm_group V] [vector_space K V] {ι : Type w} 
[fintype ι] {b : ι → V} (h : is_basis K b)[W : submodule K V ] : true := begin 
    let F := exists_is_basis K W,
    rcases F with ⟨B,hyp⟩,
    have  f : linear_independent K (λ (i : B), submodule.subtype W i.val ),
    let f :=  linear_independent.image_subtype hyp.1,
    
    
    
    --- linear_independant image injective avec l'injection canonique !
    
            
        
    --let H := @exists_subset_is_basis K  V _ _ _  _, --- probleme de convertion de set


end
end vector_space