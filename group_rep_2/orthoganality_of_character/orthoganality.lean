import schur_theorem.schur
import data.complex.basic
import Tools.tools
import basic_definitions.matrix_representation
import Reynold_operator.reynold_scalar_product
open_locale big_operators
universes u v w w'
variables {G : Type u} [group G]  
          {X : Type v} [fintype X][decidable_eq X] 
          {ρ : group_representation G ℂ (X → ℂ)}
open Irreductible Schur₂ morphism.from_irreductible equiv_morphism
--set_option trace.simplify  true
lemma terrrrr ( a : ℕ ) (ζ :  ℂ ) : a • ζ = (a : ℂ ) • ζ := 
begin 
    exact add_monoid.smul_eq_mul a ζ,
end

/--
    We admit a theorem 
-/
theorem eigen_values_exist : ∀ f : (X → ℂ ) →ₗ[ℂ] (X → ℂ),  ∃ t : ℂ, ∃ φ  : (X → ℂ ), 
 (φ ≠ 0) ∧  (f φ + t • φ =0) := by admit  

theorem Schur_on [Irreductible ρ] (f : ρ ⟶ ρ) : 
        ∃ t : ℂ, f + t • 1  = 0  := 
begin 
    rcases eigen_values_exist f.ℓ with ⟨t,⟨ φ, hyp_t⟩ ⟩,
    use t, 
    apply morphism.ext, apply linear_map.ext, 
    exact Schur₂ f t φ hyp_t,
 end 
/--
    Universe Y  = Univrse X ? here i put the dsame for matrix !!!
-/
variables {Y : Type v} [fintype Y][decidable_eq Y] {ρ' : group_representation G ℂ (Y → ℂ)}
#check ker_im_equiv
def not_isomorphic (ρ : group_representation G ℂ (X → ℂ)) (ρ' : group_representation G ℂ (Y → ℂ)) :=
                      (ρ ≃ᵣ ρ') → false 
open_locale classical
theorem shu (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] : ∀ f : ρ ⟶ ρ', f = 0   
:= begin 
    by_contradiction,
    push_neg at a,rcases a with ⟨ φ, hyp ⟩, have : ∃ x, φ x ≠  0,
        simp, by_contradiction, push_neg at a, have : φ = 0, apply morphism.ext, 
        apply linear_map.ext, exact a, trivial,
    let shur := Schur₁ φ this, -- j'ai un isoso 
     apply F,exact ( ker_im_equiv φ shur),
    
end
variables [fintype G][decidable_eq G]
#check Reynold.Re ρ ρ' 
open Reynold
/--
    J'ai le même problème 
-/
theorem grall (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ']: Re ρ ρ' = 0 := 
begin 
    apply linear_map.ext,
    intros f,
    apply shu F,
end
theorem grall₁ (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] ( x : X) (y : Y) :
   Re ρ ρ' ( matrix.to_lin (ℰ  y x)) = 0 := by {rw grall F, exact rfl}


/-!
    Faire suggir les choses !  Ici on va reprendre en faisant des égalités plutot que des  = 0 ! c'est con ! 
-/
theorem grall₂ (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] ( x : X) (y : Y) : 
 ∑ s, mixte_conj ρ ρ'  (matrix.to_lin (ℰ y x)) s = 0 := 
begin 
    erw ← reynold_ext', let g := grall₁ F  x y ,
    erw g,
    exact rfl,
end
open matrix
open linear_map
 theorem grall₃ (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] ( x : X) (y : Y) :
 to_matrix (∑ s, mixte_conj ρ ρ'  (to_lin (ℰ y x)) s ) = 0 :=
 begin 
    rw grall₂ F,apply proof_strategy, rw to_lin_zero, rw to_matrix_to_lin,
 end

lemma sum_to_matrix (φ : G → ((X → ℂ) →ₗ[ℂ] (Y → ℂ ))) : to_matrix (∑ s, φ s) = ∑ s, to_matrix (φ s) := 
begin 
    apply proof_strategy,rw to_matrix_to_lin,
    erw ←  finset.sum_hom finset.univ to_lin, congr,funext,
    rw to_matrix_to_lin, exact to_lin.is_add_monoid_hom,
end  

 theorem grall₄  (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] ( x : X) (y : Y) :
(∑ s,  to_matrix (mixte_conj ρ ρ'  (to_lin (ℰ y x)) s ) )= 0 := 
begin
    rw ← sum_to_matrix,
    rw grall₃ F,
end
open_locale matrix
theorem grall₅   (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] ( x : X) (y : Y) :
(∑ s,  (to_matrix (ρ' s⁻¹ : (Y→ ℂ) →ₗ[ℂ] (Y → ℂ ) )) ⬝  (ℰ y x) ⬝  (to_matrix (ρ s : (X→ ℂ) →ₗ[ℂ] (X → ℂ ) )) )= 0 := 
begin
    apply proof_strategy,
    rw to_lin_zero,
    erw ←  finset.sum_hom finset.univ to_lin,
    conv_lhs {
        apply_congr, skip,
        rw mul_to_lin,rw mul_to_lin, rw to_matrix_to_lin, rw to_matrix_to_lin,
        erw ← mixte_conj_ext,
    }, rw grall₂ F,exact to_lin.is_add_monoid_hom,
end
/-!
    Integration de la matrix representation 
-/
open character
theorem grall₆   (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] ( x0 : X) (y0 : Y) :
(∑ s,  (mat ρ' s⁻¹ ) ⬝  (ℰ y0 x0) ⬝  (mat ρ s  ) ) = 0 :=
begin 
    erw grall₅ F,
end 
/--
    Integration du calcul monstreux 
    @[simp]theorem mul_E_mul ( N : matrix X X R) (x0 : X)(y0 : Y) ( M : matrix Y Y R) :
 N ⬝ (ℰ x0 y0 ) ⬝ M = λ x y, N x x0 * M y0 y :=
-/

theorem grall₇    (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] (x x0 : X) (y y0 : Y) :
∑ s, ((mat ρ' s⁻¹ ) y y0) * (mat ρ s x0 x ) = 0 := begin 
    conv_lhs {
        apply_congr, skip,
        erw ← mul_E_mul',
    },
    let g := sum_apply_mat (λ s,  (mat ρ' s⁻¹ ) ⬝  (ℰ y0 x0) ⬝  (mat ρ s  )) x y,
    erw ←  g,
    rw grall₆ F, exact rfl,
end
open bilin_form
/-!
    Integration  du produit scalaire  
-/

theorem 𝒪ℛ𝒯ℋ𝒪  (F : not_isomorphic ρ ρ')[Irreductible ρ ][Irreductible ρ'] : 
scalar_product G ℂ   (χ ρ ) (χ ρ' ) = 0 := 
begin 
    rw interpretation_produit_scalaire ρ ρ',
    apply finset.sum_eq_zero,
    intros, 
    rw grall F, exact rfl,
end
/--
    La mère de les grall
-/
theorem graalₒ  : 
scalar_product G ℂ  (χ ρ ) (χ ρ' ) = 
∑ (y : X × Y), ∑ (x : G), mat ρ x y.fst y.fst * mat ρ' x⁻¹ y.snd y.snd   := 
begin 
    rw scalar_product_ext, 
    conv_lhs {
        apply_congr,skip,
        rw chi_ext,
        rw chi_ext,        
        erw finset.sum_mul_sum,
    },
    erw finset.sum_comm,exact rfl,
end
 

/--
    (N ⬝ (ℰ x0 y0 ) ⬝ M) x y =  N x x0 * M y0 y
-/
theorem graal  : 
scalar_product G ℂ  (χ ρ ) (χ ρ' ) = 
∑ (y : X × Y), (∑ (s : G), ((mat ρ s) ⬝ (ℰ y.fst y.snd )  ⬝ (mat ρ' s⁻¹))) y.fst y.snd  
  := begin 
    erw  graalₒ,
    congr, funext y,
    erw  sum_apply_mat,
    congr,
    funext,
    erw ← mul_E_mul',
  end


 
theorem Schur_on' [Irreductible ρ] (f : ρ ⟶ ρ) :  
∃ t : ℂ, f +t • 1  = 0  :=
begin 
    rcases eigen_values_exist f.ℓ with ⟨t,⟨ φ, hyp_t⟩ ⟩,
    use t,  
    apply morphism.ext, apply linear_map.ext, 
    exact Schur₂ f t φ hyp_t,
 end 
#check matrix.trace X ℂ  (X → ℂ )




 


lemma homo_eq_diag (f : (X → ℂ) →ₗ[ℂ] (X → ℂ))(t : ℂ) (hyp : f + t • 1 = 0) :
(to_matrix f) = (- t) • (1 : matrix X X ℂ ) := 
begin 
    have : f = f+ t• 1+ (-t) • 1,
        simp,
    rw this, rw hyp,rw zero_add,
    apply matrix.ext,
    intros i j,
    unfold linear_map.to_matrix,simp [linear_map.to_matrix, linear_map.to_matrixₗ, matrix.one_val, eq_comm],
    split_ifs, exact rfl,rw neg_zero,
end
open Ring
theorem Schur_grall [Irreductible ρ] (f : ρ ⟶ ρ ) :
  matrix.trace X  ℂ  ℂ (linear_map.to_matrix f.ℓ) •  (1 : matrix X X ℂ) =  (fintype.card X) •  (linear_map.to_matrix f.ℓ) :=
  begin 
    rcases Schur_on' f with ⟨ζ, hyp⟩,
    have trr : f.ℓ + ζ • 1 = 0,
        change f.ℓ + ζ • (1 : ρ ⟶ ρ).ℓ  = 0,
        erw ← morphism_module.coe_smul,
        rw ← morphism_module.add_coe, rw hyp, exact rfl,
    rw homo_eq_diag f.ℓ ζ  trr, rw map_smul, rw trace_one,
    -- analyse 
    funext,simp, rw one_val,rw mul_comm, rw mul_ite, 
    rw mul_one, rw mul_zero,
    rw terrrrr,rw smul_eq_mul,rw ←  mul_assoc, rw mul_comm, rw ite_mul, rw one_mul,rw zero_mul,
    split_ifs,simp, simp,
    
end 
theorem Schur_grall_ite [Irreductible ρ] (f : ρ ⟶ ρ ) ( x y : X) : 
((fintype.card X) •  (linear_map.to_matrix f.ℓ)) x y = if x = y then matrix.trace X  ℂ  ℂ (linear_map.to_matrix f.ℓ) else 0 :=
begin 
    rw ← Schur_grall, 
    change ((trace X ℂ ℂ) (to_matrix f.ℓ)) • (1 : matrix X X  ℂ ) x y = _,
    rw one_val, rw smul_ite,congr,exact mul_one ((trace X ℂ ℂ) (to_matrix f.ℓ)),
    exact mul_zero ((trace X ℂ ℂ) (to_matrix f.ℓ)),
end
/--
    Très bon théorème qui va permettre d'aller plus vite ! 
-/
theorem Grall₁  ( x0 : X) (y0 : Y) :
   linear_map.to_matrix (Re ρ ρ' ( matrix.to_lin (ℰ  y0 x0))).ℓ  =  (∑ s,  (mat ρ' s⁻¹ ) ⬝  (ℰ y0 x0) ⬝  (mat ρ s  ) ) := begin
    apply proof_strategy,  rw to_matrix_to_lin,
    erw ← finset.sum_hom finset.univ to_lin,swap, by apply_instance,
    swap, exact to_lin.is_add_monoid_hom,
    erw reynold_ext',congr,
    funext,rw  mul_to_lin, rw mul_to_lin, erw to_matrix_to_lin, erw to_matrix_to_lin,
    exact rfl,
end
/--
    ON va l'accoquiner a
-/
theorem Graal  : 
scalar_product G ℂ  (χ ρ ) (χ ρ' ) = 
∑ (y : X × Y), (∑ (s : G), ((mat ρ' s) ⬝ (ℰ y.snd y.fst )  ⬝ (mat ρ s⁻¹))) y.snd y.fst :=
begin 
    rw graal, congr,
    funext,
    conv_lhs{
        rw sum_apply_mat,
        apply_congr,skip, erw mul_E_mul',
    },
    conv_lhs{
        erw ← scalar_product_ext G (λ x, mat ρ x y.fst y.fst )(λ x, mat ρ' x  y.snd y.snd),
        rw bilin_symm,
    },
    rw scalar_product_ext,
    rw sum_apply_mat,
    congr,
    funext, erw ← mul_E_mul',
end

/--
    Etudier la trace des matrice elemenentaires A faire dans matrix bases DO !
-/
theorem ortho₁ (ζ  : X × X)  [Irreductible ρ ]: 
(fintype.card X • (linear_map.to_matrix (Re ρ ρ ( matrix.to_lin (ℰ  ζ.snd ζ.fst))).ℓ)) ζ.snd ζ.fst  =
 (fintype.card G •  matrix.trace X  ℂ  ℂ ((ℰ ζ.snd ζ.fst)))  :=
begin
    erw  Schur_grall_ite,
    split_ifs, erw Grall₁,
    rw h,rw trace_E,rw sum_trace,
    conv_lhs{
        apply_congr,skip,
        rw matrix.trace_mul_comm, rw ← matrix.mul_assoc, 
        rw ← matrix.mul_eq_mul, rw ← matrix.mul_eq_mul,
        rw ← character.mat_mul,
        rw mul_inv_self, rw character.mat_one, rw one_mul,
        rw trace_E,
    }, rw finset.sum_const,split_ifs, exact rfl,exact rfl,
    rw trace_E, split_ifs, rw smul_zero,
end
lemma terre (a : ℕ) (ζ : ℂ) : a • ζ = (a : ℂ ) * ζ := begin
    exact terrrrr a ζ, 
end
theorem ortho₂  (ζ  : X × X)  [Irreductible ρ ]: 
fintype.card X • ( (linear_map.to_matrix (Re ρ ρ ( matrix.to_lin (ℰ  ζ.snd ζ.fst))).ℓ) ζ.snd ζ.fst)  =
 fintype.card G •  (matrix.trace X  ℂ  ℂ ((ℰ ζ.snd ζ.fst))) := begin 
    erw terre, erw terre, erw ← matrix.smul_val, 
    change (↑(fintype.card X) •   ((to_matrix ((Re ρ ρ) (to_lin (ℰ ζ.snd ζ.fst))).ℓ))) ζ.snd ζ.fst = _,
    dsimp,
    erw ← add_monoid.smul_eq_mul (fintype.card X),-- ((to_matrix ((Re ρ ρ) (to_lin (ℰ ζ.snd ζ.fst))).ℓ) ζ.snd ζ.fst),
    change (fintype.card X •   ((to_matrix ((Re ρ ρ) (to_lin (ℰ ζ.snd ζ.fst))).ℓ))) ζ.snd ζ.fst = _,
    erw ortho₁, 
    rw ← terre, exact rfl,
 end
lemma ter_coe ( a : ℕ )(hyp : a ≠ 0) : (a : ℂ )⁻¹  * a = 1 :=begin 
   erw inv_mul_cancel, simp,exact hyp,
end

lemma  maxi_terrr (a b : ℕ ) {ζ η  : ℂ } (hyp : b ≠ 0) : a • ζ = b • η →  (a : ℂ)  * (b : ℂ)⁻¹   * ζ  = η 
:= begin 
    intros, rw mul_assoc, rw mul_comm, rw  mul_assoc, rw mul_comm ζ, norm_cast,
    erw  terre a ζ  at a_1, rw a_1,unfold_coes, 
    erw mul_comm, rw terre, rw mul_comm,rw ← mul_assoc, erw ter_coe _ hyp, rw one_mul,
end

lemma ortho₃ (ζ  : X × X)  [Irreductible ρ ] (hyp : fintype.card X ≠ 0) :
  (fintype.card G : ℂ ) * (fintype.card X : ℂ)⁻¹  * (matrix.trace X  ℂ  ℂ ((ℰ ζ.snd ζ.fst))) = ( (linear_map.to_matrix (Re ρ ρ ( matrix.to_lin (ℰ  ζ.snd ζ.fst))).ℓ) ζ.snd ζ.fst) :=
 begin 
    let g := eq.symm  (ortho₂ ζ) ,
    exact maxi_terrr (fintype.card G) (fintype.card X)  (hyp) g , assumption, assumption,
 end


lemma ortho₄  [Irreductible ρ ] (hyp : fintype.card X ≠ 0) : 
 scalar_product G ℂ  (χ ρ ) (χ ρ ) = 
∑ (ζ  : X × X), (fintype.card G : ℂ ) * (fintype.card X : ℂ)⁻¹  * (matrix.trace X  ℂ  ℂ ((ℰ ζ.snd ζ.fst))) := 
begin 
    rw interpretation_produit_scalaire,
    congr,funext,
    rw ← ortho₃, exact hyp,
end
lemma  stra ( a b : ℂ ) (hyp : a ≠ 0) : b = a →  a⁻¹ * b = 1  := begin 
    intros, rw a_1, rw inv_mul_cancel, assumption,
end

lemma strar ( a b : ℕ) : a ≠ b → (a : ℂ ) ≠ (b : ℂ ) := begin 
    intros, refine function.injective.ne (nat.cast_injective) a_1,
end
/--
    Des lemmes utilises 
-/
lemma streoi ( a b : ℕ  ) : (a : ℂ )= b → a = b := begin 
    intros, apply nat.cast_inj.mp, exact a_1, by apply_instance,
end
#check int.cast
lemma stra_fin ( a b : ℕ ) : a = b → (a : ℂ ) = (b : ℂ ) := begin 
        intros, exact congr_arg coe a_1,
end
lemma 𝒪𝓇𝓉𝒽ℴ (ρ : group_representation G ℂ (X → ℂ ))  [Irreductible ρ ] (hyp : fintype.card X ≠ 0) : 
scalar_product G ℂ  (χ ρ ) (χ ρ ) = (fintype.card G : ℂ ) := 
begin 
    let g := interpretation_produit_scalaire ρ ρ,
    rw ortho₄,swap, exact hyp,
    conv_lhs {
        apply_congr, skip, rw mul_assoc,
    }, 
    erw ← finset.mul_sum, erw ← mul_one ↑(fintype.card G),congr, rw mul_one,
    erw ← finset.mul_sum,
    apply stra,
    exact function.injective.ne (nat.cast_injective) hyp,
    rw ter X  ℂ ,swap, intros, rw trace_E,split_ifs, rw h at a,trivial,exact rfl,
    conv_lhs{
        apply_congr,skip,
        rw trace_E,
    },
    rw finset.sum_ite,
    rw finset.sum_const_zero,rw add_zero,
    conv_lhs{
        apply_congr,rw finset.filter_filter,
    },rw finset.sum_const,
    erw add_monoid.smul_eq_mul, rw mul_one,
    apply congr_arg coe,
    rw GRAAL,
    rw terrrrrrrrr,simpa,
    ---- Simpa is sympathique :D  
end
example (ρ : group_representation G ℂ (X → ℂ )) [Irreductible ρ ] 
                (hyp : fintype.card X ≠ 0) : 

    (↑(fintype.card G))⁻¹ * ∑ (t : G), χ ρ t * χ ρ t⁻¹ = 1 := 
begin 
    let g := 𝒪𝓇𝓉𝒽ℴ ρ hyp,
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