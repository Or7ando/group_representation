import linear_algebra.basic
import data.fintype.basic
import algebra.big_operators
import data.finset algebra.big_operators
import linear_algebra.basic linear_algebra.finite_dimensional    
import algebra.module  
import data.equiv.basic
universes u v w w'
infix ` * ` := linear_map.comp   ----  his there a standart notation ? 
open linear_map
namespace TEST
variables {G : Type u } [group G][fintype G]  {R : Type v}[comm_ring R] 
{M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M']
          (φ : G → (M →ₗ[R]M'))
          (f : M' →ₗ[R]M')
          (g : M →ₗ[R]M) 
variables (a : M →ₗ[R]M') (x : M)

@[simp]lemma Sum_map (x: M) :  f(finset.univ.sum (λ g, φ g x)) = finset.univ.sum (λ g, (f (φ g x))) := begin 
    erw map_sum,
    --rw @map_sum R M' M' G _ _ _ _ _ f _  (λ g, φ g x),
end   
@[simp]lemma Sum_apply (x : M) : (finset.sum finset.univ φ) x = (finset.sum finset.univ (λ g, φ g x)) := begin 
    erw  sum_apply, --finset.univ φ x,
end
@[simp]lemma Sum_comp_left : f * (finset.univ.sum φ) = finset.univ.sum (λ g, (f * (φ g ))) := begin 
    ext,rw linear_map.comp_apply, rw Sum_apply, rw Sum_apply, rw Sum_map, exact rfl, 
end

lemma Sum_comp_right  :  (finset.univ.sum φ) * g = finset.univ.sum (λ s, ((φ s)  * g)) := begin 
    ext, rw linear_map.comp_apply, erw sum_apply,erw sum_apply,exact rfl,
end
notation `Σ ` := finset.sum finset.univ  
#check (@finset.univ G) 
#check @map_sum R M' M' G _ _ _ _ _ f _  (λ g, φ g x)
/-
map_sum :
  ∀ {R : Type u_1} {M : Type u_2} {M₂ : Type u_3} {ι : Type u_4} [_inst_1 : ring R] [_inst_2 : add_comm_group M]
  [_inst_3 : add_comm_group M₂] [_inst_5 : module R M] [_inst_6 : module R M₂] (f : M →ₗ[R] M₂)
  {t : finset ι} {g : ι → M}, ⇑f (finset.sum t g) = finset.sum t (λ (i : ι), ⇑f (g i))
-/
end TEST

namespace TEST2
def Sum {R : Type u}[add_comm_monoid R]{X : Type v}[fintype X](g : X → R) : R  := finset.sum (finset.univ) g 
notation `Σ` := finset.sum (finset.univ)
variables {G : Type u } [group G][fintype G]  {R : Type v}[comm_ring R] 
{M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M']
          (φ : G → (M →ₗ[R]M'))
          (f : M' →ₗ[R]M') 
lemma Sum_comp_left : f * (Σ φ) = Σ  (λ g, (f * (φ g ))) := begin 
    rw TEST.Sum_comp_left, 
end
end TEST2