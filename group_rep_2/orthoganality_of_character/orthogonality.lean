import schur_theorem.schur
import data.complex.basic
import Tools.tools
import Tools.eigen_value
import linear_algebra.caracteristic_polynomial
import basic_definitions.matrix_representation
import basic_definitions.equiv
import permutation_representation.regular_representation
import Reynold_operator.reynold_scalar_product
set_option pp.generalized_field_notation false
open_locale big_operators
universes u v w w'
open car_pol  
variables {G : Type u} [group G]  
          {X : Type v} [fintype X][decidable_eq X] 
          {ρ : group_representation G ℂ (X → ℂ)}
open  Schur₂ morphism.from_irreductible equiv_morphism shur₁_comm_ring stability pequiv
open  Reynold
/--
   
-/
theorem eigen_values_exist (hyp : 0 < fintype.card X ) : ∀ f : (X → ℂ ) →ₗ[ℂ] (X → ℂ),  ∃ t : ℂ, ∃ φ  : (X → ℂ ), 
 (φ ≠ 0) ∧  (f φ + t • φ =0) := begin
    intro f,
    rcases eigen_values_exist_mat hyp (linear_map.to_matrix f) with ⟨w, hyp_w⟩  ,
    let t := exist_ker_not_trivial (f+ w • 1),
    use w,  apply t,
    have : linear_map.to_matrix f + w • 1 = linear_map.to_matrix (f + w • 1),
        rw to_matrix_add, rw to_matrix_smul, rw to_matrix_one,
    rw ← this, assumption,
 end

theorem Schur_on (hyp : 0 < fintype.card X ) [Irreductible ρ] (f : ρ ⟶ᵣ ρ) : 
        ∃ t : ℂ, f + t • 1  = 0  := 
begin 
    rcases eigen_values_exist hyp f.ℓ with ⟨t,⟨ φ, hyp_t⟩ ⟩,
    use t, 
    apply morphism.ext, apply linear_map.ext, 
    exact Schur₂ f t φ hyp_t,
 end 
/--
    Universe Y  = Univrse X ? here i put the dsame for matrix !!!
-/
variables {Y : Type v} [fintype Y][decidable_eq Y] {ρ' : group_representation G ℂ (Y → ℂ)}

variables [fintype G][decidable_eq G]


open matrix linear_map character
open_locale matrix

/--
Le theorem vit sans hypothèse 
-/
theorem 𝒪ℛ𝒯ℋ𝒪  (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] : 
scalar_product G ℂ   (χ ρ ) (χ ρ' ) = 0 := 
begin 
    rw interpretation_produit_scalaire ρ ρ',
    apply finset.sum_eq_zero,
    intros, 
    rw Reynold_is_zero F, exact rfl,
end


open Ring



lemma proof_strategy₃  (a b: ℂ ) (hyp : b   ≠ 0) (M N : matrix X X ℂ ): a • M = b • N → N = (b ⁻¹ * a) • M := 
begin
    intros, rw mul_smul_mat, rw a_1,
     erw ← mul_smul_mat, rw inv_mul_cancel, rw one_smul, exact hyp,
end

/--
    Faire mieux !!!  hyp et hyp'
-/
lemma Schur_grallr [Irreductible ρ] (f : ρ ⟶ᵣ ρ ) (hyp' : 0 < fintype.card X ) (hyp : fintype.card X ≠ 0)  :  
(to_matrix f.ℓ) = ((fintype.card X : ℂ)⁻¹ * (matrix.trace X  ℂ  ℂ (linear_map.to_matrix f.ℓ))) •  1
:= begin 
    apply proof_strategy₃,
    refine function.injective.ne (nat.cast_injective) hyp,
    rcases Schur_on hyp' f with ⟨ζ, hyp⟩,
    have  : f.ℓ + ζ • (1 : ρ ⟶ᵣ ρ).ℓ = 0, 
        erw ← morphism_module.coe_smul,
        rw ← morphism_module.add_coe, rw hyp, exact rfl,
    rw homo_eq_diag f.ℓ ζ  this, rw map_smul, rw trace_one,
    erw ← mul_smul_mat,
    rw mul_comm,
    exact rfl,
end


lemma proof_strategy₂ (a : ℂ ) {  c d : ℂ } :  c = d  →    a * c = a * d := congr_arg (λ x, a * x)


lemma Reynold_E  (ρ : group_representation G ℂ (X → ℂ)) [Irreductible ρ ](hyp' : 0 < fintype.card X ) (hyp : fintype.card X ≠ 0)(x : X × X)  : 
to_matrix ((Re ρ ρ) (to_lin (ℰ x.snd x.fst))).ℓ x.snd x.fst =   ↑(fintype.card G) * (↑(fintype.card X))⁻¹ * (trace X ℂ ℂ) (ℰ x.snd x.fst) :=
begin 
    rw Schur_grallr ((Re ρ ρ) (to_lin (ℰ x.snd x.fst)))hyp'  hyp,
    -- clean up
    rw [ smul_val,  one_val, mul_assoc,  mul_comm ↑(fintype.card G),  mul_assoc],
    apply proof_strategy₂ (↑(fintype.card X))⁻¹,
    rw to_matrix_Reynold_E, 
    rw trace_E, split_ifs,
        -- (trace ∑ = ∑ trace) and (trace conjugate = trace) and (trace ℰ x x = 1) 
        {rw h,rw trace_Reynold_E,},
        -- trivial 
        {repeat {rw mul_zero}}, 
end


lemma 𝒪𝓇𝓉𝒽ℴ (ρ : group_representation G ℂ (X → ℂ ))  [Irreductible ρ ] (hyp' : 0 < fintype.card X )(hyp : fintype.card X ≠ 0) : 
scalar_product G ℂ  (χ ρ ) (χ ρ ) = (fintype.card G : ℂ ) := 
begin 
    rw interpretation_produit_scalaire,
    conv_lhs{
        apply_congr, skip, 
        rw Reynold_E ρ hyp' hyp,
        rw trace_E,
    }, 
    rw ← finset.mul_sum,
    -- ∑ x  : X × X, ite (x.fst  = x.snd) 1 0 = card X ... the diagonal equivalence 
    erw sum_diagonal_one_eq_cardinal X ℂ,
    rw mul_assoc,rw inv_mul_cancel,rw mul_one,
    exact function.injective.ne (nat.cast_injective) hyp,
end

theorem scalar_product_equiv (ρ : group_representation G ℂ (X → ℂ ))  [Irreductible ρ ] (ρ' : group_representation G ℂ (Y → ℂ ))  
(iso : is_isomorphic ρ ρ' ) [Irreductible ρ ] (hyp' : 0 < fintype.card X )
(hyp : fintype.card X ≠ 0) : scalar_product G ℂ  (χ ρ ) (χ ρ' ) = (fintype.card G : ℂ ) := begin 
    rw ←  equivalence.carac_eq' ρ ρ' iso,
    erw 𝒪𝓇𝓉𝒽ℴ ρ,exact hyp', exact hyp,
end
noncomputable instance : decidable (is_isomorphic ρ ρ' ) := begin 
    exact classical.dec (is_isomorphic ρ ρ'),
end
theorem scalar_product_ite (ρ : group_representation G ℂ (X → ℂ ))  [Irreductible ρ ] (ρ' : group_representation G ℂ (Y → ℂ ))  
 [Irreductible ρ' ](hyp' : 0 < fintype.card X )
(hyp : fintype.card X ≠ 0) :  scalar_product G ℂ  (χ ρ ) (χ ρ' ) = if (is_isomorphic ρ ρ') then (fintype.card G : ℂ ) else 0 
:= begin 
    split_ifs,  apply scalar_product_equiv (by assumption), exact h, exact hyp', exact hyp,
    let  := non_is_isomorphic_eq_not_isomorphic ρ ρ' h,
    exact 𝒪ℛ𝒯ℋ𝒪 this , 
end 


example (ρ : group_representation G ℂ (X → ℂ )) [Irreductible ρ ] 
                (hyp : fintype.card X ≠ 0) (hyp' : 0 < fintype.card X ) : 

    (↑(fintype.card G))⁻¹ * ∑ (t : G), χ ρ t * χ ρ t⁻¹ = 1 := 
begin 
    let g := 𝒪𝓇𝓉𝒽ℴ ρ hyp' hyp,
    rw scalar_product_ext at g,
    rw g, apply inv_mul_cancel,rw coe_to_lift, simp,
     intro, 
    let r := finset.card_eq_zero.mp a, have : ( 1 : G) ∈ finset.univ, --- grrrrrrrrrr
        refine finset.mem_univ 1, 
    finish,
end
example (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] : 

         (↑(fintype.card G))⁻¹ *   ∑ (t : G), χ ρ t * χ ρ' t⁻¹ = 0  := 
begin 
    let g := 𝒪ℛ𝒯ℋ𝒪 F,
    rw scalar_product_ext at g,
    rw g, erw mul_zero,
end

#check Regular.Regular_representation
/--
    OKay for other ring than `ℂ` !  
-/
theorem scalar_product_with_regular (ρ : group_representation G ℂ (X → ℂ )) : 
scalar_product G ℂ (χ ρ) (χ (Regular.Regular_representation G ℂ )) =  (χ ρ 1) * (fintype.card G) := 
begin 
    rw scalar_product_ext,
    conv_lhs{
        apply_congr,skip,
        rw Regular.character_of_regular_representation, rw mul_ite, rw mul_zero,
    },
    rw finset.sum_ite,
     rw finset.sum_const_zero, rw add_zero,simp,rw finset.sum_filter,
     rw finset.sum_ite_eq',split_ifs,
     rw χ_one,
     let t := (finset.mem_univ (1 : G)),trivial,
end