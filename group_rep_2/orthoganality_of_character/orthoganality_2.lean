import orthoganality_of_character.orthogonality   
noncomputable theory
set_option pp.generalized_field_notation false
open_locale big_operators
universes u v w w'
open car_pol
open  Schur₂ morphism.from_irreductible equiv_morphism shur₁_comm_ring stability 
open  Reynold
open matrix linear_map character
namespace decomposition
variables {G : Type u} [group G]  [fintype G][decidable_eq G]
          {X : Type v} [fintype X][decidable_eq X] 
          (ρ : group_representation G ℂ (X → ℂ))
          {Y : Type w} [fintype Y][decidable_eq Y]
          (ι : Type v) [fintype ι][decidable_eq ι] (M : ι → Type w)
          [Π i, fintype(M i)][Π i,decidable_eq (M i)]
          (φ : Π i,group_representation G ℂ  (M i → ℂ )) [Π i, Irreductible (φ i) ]
          {π  : group_representation G ℂ (Y → ℂ)} [Irreductible π  ]
#check finset
def  is_decomposition := χ ρ = ∑ i, χ (φ i)  ---- baby decomposition ! 
#check   subtype (λ i : ι , is_isomorphic ρ (φ i))
open_locale classical
instance  : fintype { i : ι // is_isomorphic ρ (φ i)  } := begin 
    exact set_fintype (λ (x : ι), nonempty (ρ ≃ᵣ φ x)),
end
end decomposition
open decomposition
variables {G : Type u} [group G]  [fintype G][decidable_eq G]
          {X : Type v} [fintype X][decidable_eq X] 
          (ρ : group_representation G ℂ (X → ℂ))
          {Y : Type w} [fintype Y][decidable_eq Y]
          (ι : Type v) [fintype ι][decidable_eq ι] (M : ι → Type w)
          [Π i, fintype(M i)][Π i,decidable_eq (M i)]
          (φ : Π i,group_representation G ℂ  (M i → ℂ )) [Π i, Irreductible (φ i) ]
          {π  : group_representation G ℂ (Y → ℂ)} [Irreductible π  ]
theorem scal (hyp : is_decomposition ρ ι M φ  ) (hyp' : 0 < fintype.card Y ) (hyp'' : fintype.card Y ≠ 0) : 
    scalar_product G ℂ (χ (π )) (χ (ρ )) = (fintype.card { i : ι  | is_isomorphic π   (φ    i)  }) * ↑(fintype.card G)  :=
begin 
    unfold is_decomposition at *, rw hyp,
    rw bilin_form.map_sum_right, 
    let g := λ i,  scalar_product_ite  π (φ i)hyp'  hyp'',
    conv_lhs{
        apply_congr,skip,
        rw g,
    },
    rw finset.sum_ite, rw finset.sum_const_zero, rw add_zero,
    rw finset.sum_const, rw add_monoid.smul_eq_mul, 
    erw fintype.card_of_subtype _, intros,
    split,  intros, rw finset.mem_filter at a, exact a.2,
    intros, rw finset.mem_filter, split, exact finset.mem_univ _,
    exact a,
end
namespace regular
variables {Z : Type w} [fintype Y][decidable_eq Y]
          (t : Type u) [fintype t][decidable_eq t] (Mt : t → Type w)
          [Π i, fintype(Mt i)][Π i,decidable_eq (Mt i)]
          (ψ  : Π i,group_representation G ℂ  (Mt i → ℂ )) [Π i, Irreductible (ψ i) ]
theorem scal_regular  (hyp : is_decomposition (Regular.Regular_representation G ℂ ) t Mt ψ   )(hyp'' :0 < fintype.card Y ) (hyp' : fintype.card Y ≠ 0): 

    (χ π  1) * ↑(fintype.card G) = (fintype.card { i : t | is_isomorphic π   (ψ   i)  }) * ↑(fintype.card G) := 
begin 
    erw ← scal (Regular.Regular_representation G ℂ ) t Mt ψ hyp _,
    rw scalar_product_with_regular, by assumption, by assumption, 
    exact hyp'',
    end
end regular

