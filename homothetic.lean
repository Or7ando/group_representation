import .group_representation
import .morphism  
import ring_theory.algebra
open algebra
open linear_map 
universe variables u v w 
variables {G : Type u}[group G]   {R : Type v}[comm_ring R] {M : Type w} 
[add_comm_group M] [module R M]  
namespace homothetic 
variables  (ρ : group_representation G R M)

open morphism
/-
  Make an R algebra ? subalgebra of sub.type ! To check 
-/

def add ( f g : ρ ⟶ ρ ) : ρ ⟶  ρ  := {
    ℓ := f.ℓ +g.ℓ, 
    commute := begin intros k, 
        ext,simp, 
        erw commute_apply,erw commute_apply ρ,  exact rfl,
     end
}
def spectral (t : R)(f  :  ρ ⟶ ρ)   :  ρ ⟶ ρ  := { ℓ := t • f.ℓ,
  commute := begin 
        intros g,ext,simp, erw commute_apply, exact rfl,
  end }

instance has_add_morphism : has_add ( ρ ⟶ ρ ) := { add := add ρ  }  
instance has_scalar_morphism: has_scalar R ( ρ ⟶ ρ ) := { smul := spectral ρ  }
def id  :=  𝟙 ρ 
lemma add_ext ( f g : ρ ⟶ ρ ) : (f+g).ℓ = f.ℓ + g.ℓ := rfl
lemma one_ext : (𝟙 ρ ).ℓ =linear_map.id :=rfl
lemma smul_ext (t : R)(f  :  ρ ⟶ ρ) : (t • f).ℓ  = t • f.ℓ := rfl  
def test (t : R)(f  : ρ ⟶ ρ) := f + t • 𝟙 ρ 

end homothetic
#check  mul_sub_left_distrib