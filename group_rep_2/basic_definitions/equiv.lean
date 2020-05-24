import basic_definitions.morphism
universe variables u v w w'

open linear_map 
 
namespace equiv_morphism
variables {G : Type u} [group G] 
          {R : Type v} [ring R] 
          {M : Type w}   [add_comm_group M]  [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'] 

/--
  an equiv`f : ρ ≃ᵣ π` between representation is a linear equiv `f.ℓ : M(ρ) ≃ₗ[R] M(π)` satisfying 
    `f.ℓ ∘   ρ g  = π g  ∘   f.ℓ` has function on `linear_map` !  
-/
structure G_equiv (ρ : group_representation G R M) (π : group_representation G R M') : Type (max w w') := 
(ℓ : M ≃ₗ[R] M')
(commute : ∀(g : G),  ↑ℓ   ⊚    ρ g  = π g  ⊚    ℓ) --- en terme d'élément ! 

infixr ` ≃ᵣ `:25 := G_equiv  

@[ext]lemma ext {ρ  : group_representation G R M}   {ρ'  : group_representation G R M'} ( f g : ρ ≃ᵣ ρ') : 
(f.ℓ)  = g.ℓ  → f = g := begin intros, cases f,cases g , congr'; try {assumption} end


def not_isomorphic (ρ : group_representation G R M) (ρ' : group_representation G R  M') :=   -- more general 
                      (ρ ≃ᵣ ρ') → false 
/--
  `is_isomorphic ρ ρ'` when nonempty(ρ ≃ᵣ ρ') 
-/
def is_isomorphic (ρ : group_representation G R M) (ρ' : group_representation G R  M') := nonempty (ρ ≃ᵣ ρ') 

lemma non_is_isomorphic_eq_not_isomorphic (ρ : group_representation G R M) (ρ' : group_representation G R  M') : 
¬ (is_isomorphic ρ ρ') → (not_isomorphic ρ ρ') := begin 
  intros, intro,unfold is_isomorphic at  *, 
  have : nonempty (ρ ≃ᵣ ρ'),
    use a_1, trivial,
end 
/-!
  an equiv`f : ρ ≃ᵣ π` induce a morphism of representation. 
-/variables  {ρ  : group_representation G R M}   {ρ'  : group_representation G R M'} 
instance : has_coe (ρ ≃ᵣ ρ')(ρ ⟶ᵣ ρ') := ⟨λ f, { ℓ := f.ℓ , commute :=  f.commute, }  ⟩ 

open_locale classical



/-!
    Let `f : M ≃ₗ[R] M'` a `linear_equiv` and `ρ : G → GL R M` a representation, 
    we can construct a representation `image` and a `representation equiv`
-/

open linear_equiv
lemma ker_and_range_trivial_to_bijective (f : M →ₗ[R]M')  (hyp : ker f = ⊥  ∧ range f = ⊤) : function.bijective f :=  begin 
  split,refine ker_eq_bot.mp  hyp.1,
        refine range_eq_top.mp  hyp.2,
end

noncomputable def gker (f : M →ₗ[R]M') (certif  : ker f = ⊥  ∧ range f = ⊤)  :  M ≃ M' :=  { 
  to_fun    := f,
  inv_fun   := function.surj_inv (ker_and_range_trivial_to_bijective f certif).2,
  left_inv  := function.left_inverse_surj_inv (ker_and_range_trivial_to_bijective f certif), 
  right_inv := function.right_inverse_surj_inv (ker_and_range_trivial_to_bijective f certif).right,
}
#where
lemma gker_ext (f : M →ₗ[R]M') (hyp : ker f = ⊥  ∧ range f = ⊤) : (gker f hyp).to_fun = f := rfl


noncomputable lemma ker_im_equiv'' (f : M →ₗ[R]M') (hyp : ker f  = ⊥  ∧ range f  = ⊤) : M ≃ₗ[R] M'  :=  { 
  to_fun    := f  ,
  add       := f.map_add ,
  smul      := f.map_smul,
  inv_fun   := (gker f  hyp).inv_fun  ,
  left_inv  := begin let g := (gker f hyp).left_inv, erw ← (gker_ext f  hyp), exact g end, 
  right_inv := begin let g := (gker f hyp).right_inv, erw ← (gker_ext f  hyp), exact g end, 
}
lemma ker_im_equiv_ext''  (f : M →ₗ[R]M') (hyp : ker f  = ⊥  ∧ range f  = ⊤) : 
linear_equiv.to_linear_map(ker_im_equiv'' f hyp) = f := begin 
  ext, dunfold ker_im_equiv'', exact rfl,
end
variables (f : M ≃ₗ[R] M')
lemma linear_equiv_compo_id (f : M ≃ₗ[R] M') : (linear_equiv.to_linear_map f) ⊚ (linear_equiv.to_linear_map f.symm) = linear_map.id := begin
  ext, change (f.to_fun ∘  f.symm.to_fun) x = x,
  let t := f.6,exact  t x, 
end
noncomputable lemma ker_im_equiv' (f : ρ ⟶ᵣ ρ') (hyp : ker f.ℓ  = ⊥  ∧ range f.ℓ  = ⊤) : M ≃ₗ[R] M'  :=  { 
  to_fun    := f.ℓ  ,
  add       := f.ℓ.map_add ,
  smul      := f.ℓ.map_smul,
  inv_fun   := (gker f.ℓ  hyp).inv_fun  ,
  left_inv  := begin let g := (gker f.ℓ hyp).left_inv, erw ← (gker_ext f.ℓ  hyp), exact g end, 
  right_inv := begin let g := (gker f.ℓ hyp).right_inv, erw ← (gker_ext f.ℓ  hyp), exact g end, 
}
noncomputable lemma ker_im_equiv (f : ρ ⟶ᵣ ρ') (hyp : ker f.ℓ  = ⊥  ∧ range f.ℓ  = ⊤) : ρ ≃ᵣ ρ' := { 
  ℓ        := (ker_im_equiv' f hyp),
  commute  := begin intros, dunfold ker_im_equiv',erw f.commute, exact rfl end 
}

local notation  f ` leq ` g := linear_equiv.trans g f

@[simp]lemma eq_mul (ρ : group_representation G R M) ( g g' : G) : ρ (g * g') = (ρ g ⊚ ρ g') := begin 
    erw ρ.map_mul, exact rfl,
end
variables (f : M ≃ₗ[R] M') 
@[simp] lemma mul_inv (f : M ≃ₗ[R] M') : (f leq f.symm) = linear_equiv.refl R M' := begin
    ext, rw refl_apply,rw trans_apply, simp,
end
lemma mul_eq_mul (f g : M ≃ₗ[R] M ) : (f leq g) = f * g := begin 
    ext, exact rfl,
end 



def image (ρ : group_representation G R M) (f : M ≃ₗ[R] M') : group_representation G R M' := { 
  to_fun := λ g,  f leq   (gr.to_equiv' ρ g) leq f.symm  ,
  map_one' := begin 
        ext, dsimp, unfold gr.to_equiv', change (⇑f  ∘  (ρ 1) ∘  ⇑(f.symm)) x = x,
        erw ρ.map_one, simp,
     end,
  map_mul' := begin  
        intros g g',ext, dsimp, unfold gr.to_equiv', change (⇑f  ∘  (ρ (g * g')) ∘  ⇑(f.symm)) x = _, simp,exact rfl,
  end }
def image_equiv (ρ : group_representation G R M) (f : M ≃ₗ[R] M') :  ρ ≃ᵣ (image ρ f) := { ℓ := f,
  commute := begin 
        intros g, ext, unfold image, simp,exact rfl,
  end }
end equiv_morphism
#lint