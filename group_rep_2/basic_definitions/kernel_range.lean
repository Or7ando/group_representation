import .sub_module
universe variables u v w w' 

variables {G : Type u} [group G] {R : Type v}[ring R] 
variables {M1 : Type w}  [add_comm_group M1] [module R M1]
          {M2 : Type w'} [add_comm_group M2] [module R M2] 
          {ρ1 : group_representation G R M1} 
          {ρ2  : group_representation G R M2}
          (f  : ρ1 ⟶ᵣ  ρ2 )

open stability morphism linear_map
namespace Kernel
instance ker_is_stable_submodule : stable_submodule ρ1 (ker f.ℓ) := { 
stability := 
    begin 
        intros g x hyp, erw mem_ker at *, 
        change (f.ℓ  ⊚  (ρ1 g)) x = _,
        erw f.commute, change(ρ2 g) (f.ℓ x) = 0, 
        rw hyp, exact (ρ2 g).map_zero,
    end
} 

/-!
    The Kernel of `f : ρ1 ⟶ᵣ ρ2` has representation.
-/

def ker : group_representation G R (ker f.ℓ) := Res ρ1 
end Kernel

namespace range
open linear_map
/--
    Range is stable. Let `y ∈ Im f`, let `g ∈ G`, we want : `ρ g y ∈ Im f`. 
    Take `x ∈ M1` s.t `f x = y`.  We have (from `f.commute`) :
            `(f ∘ ρ1 g) x = ρ2 g ∘ f x`
    i.e `ρ2 g y = f ( ρ1 g x)` and so  `ρ2 g y ∈ Im f` 
-/

instance  : stable_submodule ρ2 (range (f.ℓ)) := { 
stability := 
    begin
        intros g y hyp, rw mem_range at  *, 
        rcases hyp with ⟨z , hyp ⟩, rw ← hyp, use (ρ1 g) z,  
        change (f.ℓ ⊚  ρ1 g) z = _, rw f.commute, exact rfl,
    end
}
/--
  For a morphism `f : ρ1 ⟶ᵣ ρ2` between `representation` we define a sub representation of `M2`
-/
def Range  : group_representation G R (range f.ℓ) := Res ρ2 

end range 