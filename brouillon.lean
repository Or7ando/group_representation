namespace morphism_composition
/-
    Goal to make effective the composition
-/ 
open morphism 
variables {M1 : Type w}  [add_comm_group M1] [module R M1]
          {M2 : Type w'} [add_comm_group M2] [module R M2] 
          {M3 : Type w''} [add_comm_group M3] [module R M3]
          {ρ1 : group_representation G R M1} 
          {ρ2  : group_representation G R M2} 
          {ρ3 : group_representation G R M3}
          {M4 : Type w'''} [add_comm_group M4] [module R M4] 
          {ρ4 : group_representation G R M4}

lemma 𝒞_o_e_r_s_i_o_n (f : M1 →ₗ[R] M2)(g : M2→ₗ[R] M3) : ⇑ (g ⊚ f)  = (⇑g ∘ ⇑f)  := rfl
lemma 𝒞_o_e_r_s_i_o_n₂ (f : M1 ≃ₗ[R] M1)(g : M1→ₗ[R] M1) : ⇑(g *  (f : M1 →ₗ[R]M1) )  = (⇑g ∘  ⇑f)  := rfl

lemma Endomorphism.apply (ρ : group_representation G R M1) ( f : Endomorphism ρ ) (x : M1) (g : G) :
f.ℓ (ρ g x) =  ρ g (f.ℓ x) := begin 
  erw ← function.comp_apply ⇑f.ℓ ⇑(ρ g) x, erw ← 𝒞_o_e_r_s_i_o_n₂ ((ρ g)),rw f.commute, exact rfl,
end
theorem Endomorphism_to_morphism (f : Endomorphism ρ1 ) : ρ1 ⟶ ρ1 := { ℓ := f.ℓ ,
  commute := begin intros g, rw ← 𝒞_o_e_r_s_i_o_n₂ (ρ1 g ) f.ℓ, rw f.commute, exact rfl,  end } 

def compo  (f2 : ρ1 ⟶ ρ2)(f3 : ρ2 ⟶ ρ3) : ρ1 ⟶ ρ3 := 
  {ℓ :=  (f3.ℓ : M2 →ₗ[R] M3) *  (f2.ℓ : M1 →ₗ[R] M2),
  commute := begin 
    intros,ext x, erw  𝒞_o_e_r_s_i_o_n _ _  ,
    iterate 4 {rw function.comp_apply},
    erw commute_apply ρ1,
    erw commute_apply ρ2,
    exact rfl,
   end} 
infixr ` ≫ `:80 := compo  -- Same sens has category  
@[simp]lemma comp_ext (f2 : ρ1 ⟶ ρ2)(f3 : ρ2 ⟶ ρ3) : (f2 ≫ f3).ℓ  = f3.ℓ  ∘  f2.ℓ := rfl
variables 
@[simp]theorem comp_assoc  (f2 : ρ1 ⟶ ρ2)(f3 : ρ2 ⟶ ρ3) (f4 : ρ3 ⟶ ρ4)  : (f2 ≫  f3) ≫ f4 = f2 ≫ (f3 ≫ f4) := 
begin ext, exact rfl, end

@[simp]lemma comp_apply (f2 : ρ1 ⟶ ρ2)(f3 : ρ2 ⟶ ρ3) ( x1 : M1 ) : (f2 ≫ f3) x1 = f3( f2 x1) := rfl

end morphism_composition
namespace One  
variables {M1 : Type w}  [add_comm_group M1] [module R M1]
          {M2 : Type w'} [add_comm_group M2] [module R M2] 
          {ρ1 : group_representation G R M1} 
          {ρ2  : group_representation G R M2}

@[ext]lemma one_ext (ρ1 : group_representation G R M1) : (one ρ1).ℓ = linear_map.id := rfl 
notation `𝟙 ` ρ1 := one ρ1
@[simp]lemma id_comp (f2 : ρ1 ⟶ ρ2) : (𝟙 ρ1) ≫ f2 = f2 := by {ext, exact rfl} 
@[simp]lemma comp_id  (f2 : ρ1 ⟶ ρ2) : f2 ≫ (𝟙 ρ2) = f2 := by { ext, exact rfl}   
end One 
