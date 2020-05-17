import data.fintype.basic
import data.set.function
import .sum_tools
import data.equiv.basic
import linear_algebra.bilinear_form
universe variables u v w 
open finset
open_locale big_operators
/--
#   Je n'aime pas du tout l'utilisation du produit scalaire car je prefere avoir une notion spécifique 
-/
variables {G :Type u} {R : Type v} [group G] [comm_ring R][fintype G]
/-!
    We define a `scalar_product` on function `G → R`
-/
def bilinear   (φ ψ : G → R  ) :=  ∑ t, (φ t) *  (ψ t⁻¹)    


variables {α : Type u} {β : Type v}
variables (φ ψ :  G → R  )
notation ` ⁅  ` φ ` | ` ψ ` ⁆ ` := bilinear φ ψ 
/--
     `《 φ + γ | ψ 》 = 《 φ | ψ 》 + 《 γ  | ψ 》`
-/
@[simp]theorem add_first  (φ γ ψ  : G → R  ) : ⁅ φ + γ | ψ ⁆  = ⁅  φ | ψ ⁆  + ⁅  γ  | ψ ⁆  := 
begin 
      unfold bilinear, erw ← multiset.sum_map_add,  --- ?
      congr,funext, erw ← right_distrib _ _ (ψ t⁻¹),
      exact rfl,
end
/--
     `《 r • φ  | ψ 》 = r • 《 φ | ψ 》`  
-/
@[simp]theorem smul_first  (r : R) (φ ψ   : G → R  ) : ⁅  r • φ  | ψ ⁆  = r • ⁅ φ | ψ ⁆  := begin 
      unfold bilinear,
     erw  finset.smul_sum,congr,funext, erw mul_assoc, exact rfl,
end
/--
     `⁅  ψ  |  φ ⁆  =  ⁅ φ | ψ ⁆`  
-/
@[simp]theorem symm_bilinear (φ ψ   : G → R  ) : ⁅  ψ  |  φ ⁆  =  ⁅ φ | ψ ⁆ := 
begin
    unfold bilinear,
    rw sum_univ_perm _ (inv_equiv), congr,
    funext, unfold inv_equiv, dsimp, rw inv_inv,rw mul_comm,
end 
/--
    `⁅ φ  | ψ + γ⁆  = ⁅  φ | ψ ⁆  + ⁅  φ   | γ  ⁆`
-/
@[simp]theorem add_snd  (φ ψ γ  : G → R  ) : ⁅ φ  | ψ + γ⁆  = ⁅  φ | ψ ⁆  + ⁅  φ   | γ  ⁆  :=begin 
    rw symm_bilinear, rw add_first, simp,
end
/--
    `⁅   φ  | r • ψ ⁆  = r • ⁅ φ | ψ ⁆
-/
@[simp]theorem smul_snd  (r : R) (φ ψ   : G → R  ) : ⁅   φ  | r • ψ ⁆  = r • ⁅ φ | ψ ⁆ := begin 
    rw symm_bilinear, rw smul_first, rw symm_bilinear,
end


def scalar_product (G : Type u)[group G] [fintype G] (R : Type v) [group G] [comm_ring R] : bilin_form  R (G → R) := { 
  bilin             := @bilinear G R _ _ _,
  bilin_add_left    := @add_first G R _ _ _,
  bilin_smul_left   := @smul_first G R _ _ _,
  bilin_add_right   := @add_snd G R _ _ _,
  bilin_smul_right  := @smul_snd G R _ _ _
}  
/--
    `scalar_product G f1 f2 =   ∑ t, (f1 t) *  (f2 t⁻¹) `
-/
lemma scalar_product_ext (G : Type u)[group G] [fintype G] {R : Type v} [group G] [comm_ring R] (f1 f2 : G → R ) : 
    scalar_product G R f1 f2 =   ∑ t, (f1 t) *  (f2 t⁻¹) := rfl 
open bilin_form
/--
    `scalar_product G f1 f2 = ⁅   f1  | f2 ⁆`
-/
lemma scalar_product_ext' (G : Type u)[group G] [fintype G] (f1 f2 : G → R ) : scalar_product G R f1 f2 = 
       ⁅   f1  | f2 ⁆ := rfl 
open bilin_form
lemma bilin_sum (X Y : Type w )[fintype X][fintype Y][decidable_eq X][decidable_eq Y] 
 (φ_l : X → (G → R ))
 (φ_r : Y → (G → R )) : 
 scalar_product G R (∑ x, φ_l x ) (∑ y, φ_r y) = ∑ x, (∑ y, scalar_product G R (φ_l x) (φ_r y)) := 
 begin 
  rw map_sum_left,
  congr,
  funext,
  rw map_sum_right,
end 
lemma bilin_symm (G : Type u)[group G] [fintype G] (f1 f2 : G → R ) : scalar_product G R f1 f2 = scalar_product G R f2 f1 :=
begin 
    rw scalar_product_ext', erw  symm_bilinear,  exact rfl,
end