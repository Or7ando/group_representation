import .group_representation
import .morphism
import .sub_module
universe variables u v w w' w'' w'''

variables {G : Type u} [group G] {R : Type v}[ring R] 
variables {M1 : Type w}  [add_comm_group M1] [module R M1]
          {M2 : Type w'} [add_comm_group M2] [module R M2] 
          {ρ1 : group_representation G R M1} 
          {ρ2  : group_representation G R M2}
          (f  : ρ1 ⟶  ρ2 )

open stability morphism
namespace Kernel
/--
   The kernel of `f : ρ1 ⟶ ρ2` is define to be the kernel of `↑f : M1 →ₗ[R] M2`
-/
def Ker := linear_map.ker (f.ℓ)   /-- bof -/
lemma Ker_ext_iff(x : M1) : x ∈ Ker f ↔ x ∈ linear_map.ker (f.ℓ)   := iff.rfl    --- brouh  not good !
lemma mem_ker (x : M1) : x ∈ Ker f ↔ f x = 0 := linear_map.mem_ker
lemma Ker_ext  (x : M1 )  : f  x = 0  →  x ∈  Ker f := 
begin 
    intros, rw Ker_ext_iff,rw linear_map.mem_ker,assumption, 
end
lemma Ker_f_mem (x : M1) : (x ∈  Ker f) →  f x  =0 := begin 
    rw ← mem_ker,intros, assumption, 
end  
/--
   The kernel of `f : ρ1 ⟶ ρ2` is an stable sub-stape of M1.
-/
theorem ker_is_stable_submodule : stable_submodule ρ1 (Ker f) := begin 
    intros g,intros x,apply Ker_ext, rw morphism.commute_apply,
    rw Ker_f_mem,rw (ρ2 g).map_zero,
    rcases x,unfold Ker at ⊢ x_property , assumption,
end
/--
    The Kernel of `f : ρ1 ⟶ ρ2` has representation.
-/
def ker : group_representation G R (Ker f) := Res (ker_is_stable_submodule f)

end Kernel
namespace range
open linear_map
/--
    Range is stable. Let `y ∈ Im f`, let `g ∈ G`, we want : `ρ g y ∈ Im f`. 
    Take `x ∈ M1` s.t `f x = y`.  We have (from `f.commute`) :
            `(f ∘ ρ1 g) x = ρ2 g ∘ f x`
    i.e `ρ2 g y = f ( ρ1 g x)` and so  `ρ2 g y ∈ Im f` 
-/

theorem range_is_stable_submodule : stable_submodule ρ2 (range (f.ℓ  : M1→ₗ[R] M2)) := begin
    intros g,intros y,rcases y with ⟨y, ⟨x,hyp⟩⟩,  
    apply linear_map.mem_range.mpr,
        use ρ1 g x, 
    erw commute_apply,
    exact congr_arg ⇑(ρ2 g) hyp.right, 
end
/--
  For a morphism `f : ρ1 ⟶ ρ2` between `representation` we define a sub representation of `M2`
-/
def Range  : group_representation G R (range (f.ℓ  : M1→ₗ[R] M2)) := Res (range_is_stable_submodule f)

end range 