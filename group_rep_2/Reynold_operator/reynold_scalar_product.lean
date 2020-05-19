import Reynold_operator.reynold
import Tools.tools  
import basic_definitions.matrix_representation  
open_locale big_operators
open_locale matrix
set_option pp.generalized_field_notation false
open Reynold linear_map matrix character  
universes u v w   
/--
    Data for the file. Here we make the assumtion that `X` and `Y` live in the same universe 
    because of `matrix X Y R` that require this.
-/
variables {G : Type u} [group G][fintype G][decidable_eq G] {R : Type v}  [comm_ring R]
          {X : Type w} [fintype X][decidable_eq X] (ρ : group_representation G R (X → R))
          {Y : Type w} [fintype Y][decidable_eq Y] (ρ' : group_representation G R (Y → R))

/-!
#   Interpretation of scalar product in term of Reynold operator.  
*   I recall the theory : 
*           let `ρ : G → GL( X → R)` and `ρ' : G → GL (Y → R)` with the variables above.
*           let `φ ψ : G → R `. 
*     then  `scalar_product G R φ ψ :=  ∑ t, (φ t) *  (ψ t⁻¹)` 
*     We define `χ : group_representation G R (X → R) →  G → R := trace to_matrix (ρ g)` 
*     Note for the moment we don't invert `card G` 
*     We define `Reynold operator : (X → R →ₗ[R] Y → R) →ₗ[R]  ρ ⟶ ρ'`
*     The definition is : `Re f := ∑ g : G,  ρ' g⁻¹ ∘ f ∘ ρ  g`
*     The next theorem formalize : 
*     `∑ g, (χ ρ g) * (χ  ρ' g⁻¹) = ∑ g, ( ∑ x : X,  to_matrix ( ρ g) x x ) ( ∑ y : Y, to_matrix (ρ' g⁻¹ ) y y)`
*                                ` = ∑ (x,y) : X × Y,  ∑ g, to_matrix ( ρ g) x x ) ( ∑ y : Y, to_matrix (ρ' g⁻¹ ) y y)`
*                                `  = ∑ (x,y) : X × Y,   to_matrix (Re ρ ρ' ( to_lin (ℰ  y x)  )).ℓ y x`
*           Where `ℰ y x` is the `elementary matrix !
*           see the files `tools.matrix` for the calculus. 
*     The fact is : Reynold operator is quasi trivial in two case 
*           1. If ` not (ρ ≃ᵣ ρ')` (not isomorphic) and ` ρ ρ' : irreducible`. 
*               If this case `Reynold opérator` is `0`. That depend of the theorem `Schur₁` in basic definition.irreducible
*                And we can calculate scalar product with this theorem and it's zero.   
*           2. if ` (ρ = ρ')` (equal) and ` ρ : irreducible` and " algebricaly closed base field ". 
*                in this case, `Reynold opérator` send a morphism `f` to an λ • 1  and we can compute.  
-/
/-!
    Wihout condition : 
    `to_matrix (Re ρ ρ' ( to_lin (ℰ  y0 x0)))  =  (∑ s,  (mat ρ' s⁻¹ ) ⬝  (ℰ y0 x0) ⬝  (mat ρ s  ) )`
-/




theorem to_matrix_Reynold_E  ( x0 : X) (y0 : Y) :
  linear_map.to_matrix (Re ρ ρ' ( to_lin (ℰ  y0 x0))).ℓ  =  (∑ s,  (mat ρ' s⁻¹ ) ⬝  (ℰ y0 x0) ⬝  (mat ρ s  ) ) := 
begin
    rw reynold_ext', rw to_matrix_sum,
    congr,funext w,rw mixte_conj_ext,
    rw to_matrix_mul, rw to_matrix_mul, rw to_lin_to_matrix,
    exact rfl,
end


theorem interpretation_produit_scalaire : 
scalar_product G R (χ ρ ) (χ ρ' ) = ∑ (y : X × Y), to_matrix (Re ρ ρ' ( to_lin (ℰ  y.snd y.fst)  )).ℓ y.snd y.fst
:= 
begin
    rw scalar_product_ext,
    conv_lhs{
        apply_congr,skip, 
        rw chi_ext,
        rw chi_ext,
        erw finset.sum_mul_sum,
    },
    erw finset.sum_comm,
    congr,funext,
    conv_lhs{
        apply_congr,skip, rw mul_comm,
        rw ← mul_E_mul',
    }, 
       rw to_matrix_Reynold_E,
       rw sum_apply_mat, 
end

theorem trace_Reynold_E ( x : X) : matrix.trace X R R (∑ s,  (mat ρ s⁻¹ ) ⬝  (ℰ x x) ⬝  (mat ρ s  ) )  = fintype.card G := 
begin 
    rw sum_trace,
    conv_lhs{
        apply_congr,skip,
        rw trace_conj,
        rw trace_E,rw if_pos rfl,
    },
    rw finset.sum_const, rw add_monoid.smul_eq_mul, rw mul_one, exact rfl,
end