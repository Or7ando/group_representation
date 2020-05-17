import basic_definitions.morphism
universe variables u v w w'

open linear_map 
 
namespace equiv_morphism
variables {G : Type u} [group G] {R : Type v}[ring R] 
        {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'] 

/--
  an equiv`f : ρ ≃ᵣ π` between representation is a linear equiv `f.ℓ : M(ρ) ≃ₗ[R] M(π)` satisfying 
    `f.ℓ ∘   ρ g  = π g  ∘   f.ℓ` has function on `set`. 
-/
structure G_equiv (ρ : group_representation G R M) (π : group_representation G R M') : Type (max w w') := 
(ℓ : M ≃ₗ[R] M')
(commute : ∀(g : G),  ↑ℓ   ⊚    ρ g  = π g  ⊚    ℓ) --- en terme d'élément ! 

infixr ` ≃ᵣ `:25 := G_equiv  

@[ext]lemma ext {ρ  : group_representation G R M}   {ρ'  : group_representation G R M'} ( f g : ρ ≃ᵣ ρ') : 
(f.ℓ)  = g.ℓ  → f = g := 
begin 
    intros, 
    cases f,cases g , congr'; try {assumption},
end
/-!
  an equiv`f : ρ ≃ᵣ π` induce a morphism of representation. 
-/

def not_isomorphic (ρ : group_representation G R M) (ρ' : group_representation G R  M') :=   -- more general 
                      (ρ ≃ᵣ ρ') → false 

variables  {ρ  : group_representation G R M}   {ρ'  : group_representation G R M'} 
instance : has_coe (ρ ≃ᵣ ρ')(ρ ⟶ ρ') := ⟨λ f, { ℓ := f.ℓ , commute :=  f.commute, }  ⟩ 
open_locale classical.prop_decidable
/-!
    Equiv is an equivalence  check in equiv !
-/

/-!
  an equiv`f : ρ ≃ᵣ π` induce a morphism of representation. 
-/

/-!
    Let `f : M ≃ₗ[R] M'` a `linear_equiv` and `ρ : G → GL R M` a representation, 
    we can construct a representation `image` and a `representation equiv`
-/
-- For the moment it's not verry clean cause of no  * notation for equiv !  
open linear_equiv
lemma jjj (f : M →ₗ[R]M')  (hyp : ker f = ⊥  ∧ range f = ⊤) : function.bijective f :=  begin 
  split,refine ker_eq_bot.mp  hyp.1,
        refine range_eq_top.mp  hyp.2,
end

noncomputable def gker (f : M →ₗ[R]M') (certif  : ker f = ⊥  ∧ range f = ⊤)  :  M ≃ M' :=  { to_fun := f,
  inv_fun := begin let G := function.surj_inv,
        let g := (jjj f certif).2,
        exact G g,
   end,
  left_inv := begin
       dsimp,exact function.left_inverse_surj_inv (jjj f certif),
  end,
  right_inv := begin 
    dsimp,exact function.right_inverse_surj_inv (jjj f certif).right,
   end}
lemma gker_ext (f : M →ₗ[R]M') (hyp : ker f = ⊥  ∧ range f = ⊤) : (gker f hyp).to_fun = f := begin 
  dunfold gker,dsimp, exact rfl,
end
noncomputable lemma ker_im_equiv' (f : ρ ⟶ ρ') (hyp : ker f.ℓ  = ⊥  ∧ range f.ℓ  = ⊤) : M ≃ₗ[R] M'  :=  { to_fun :=  f.ℓ  ,
  add := f.ℓ.map_add ,
  smul := f.ℓ.map_smul,
  inv_fun := (gker f.ℓ  hyp).inv_fun  ,
  left_inv := begin let g := (gker f.ℓ hyp).left_inv, erw ← (gker_ext f.ℓ  hyp), exact g,
         
end, 
  right_inv := begin let g := (gker f.ℓ hyp).right_inv, erw ← (gker_ext f.ℓ  hyp), exact g,
         
end, }
noncomputable lemma ker_im_equiv (f : ρ ⟶ ρ') (hyp : ker f.ℓ  = ⊥  ∧ range f.ℓ  = ⊤) : ρ ≃ᵣ ρ' := { ℓ := (ker_im_equiv' f hyp),
  commute := begin
      intros, dunfold ker_im_equiv',erw f.commute, exact rfl,
  end }
/-
Here to DOOOOOOOOOOOOOOOOOOOO 
local notation  f ` ⊚ ` g := linear_equiv.trans g f

@[simp]lemma eq_mul (ρ : group_representation G R M) ( g g' : G) : ρ (g * g') = (ρ g ⊚ ρ g') := begin 
    erw ρ.map_mul, exact rfl,
end
variables (f : M ≃ₗ[R] M') 
@[simp] lemma mul_inv (f : M ≃ₗ[R] M') : (f ⊚ f.symm) = linear_equiv.refl R M' := begin
    ext, rw refl_apply,rw trans_apply, simp,
end
lemma mul_eq_mul (f g : M ≃ₗ[R] M ) : (f ⊚ g) = f * g := begin 
    ext, exact rfl,
end 
def image (ρ : group_representation G R M) (f : M ≃ₗ[R] M') : group_representation G R M' := { 
  to_fun := λ g,  f ⊚   (ρ g : M ≃ₗ[R]M ) ⊚  f.symm  ,
  map_one' := begin
        erw ρ.map_one,ext, rw trans_apply, rw trans_apply,
        change (f ( f.symm x))  = x,
        simp,
     end,
  map_mul' := begin  
        intros g g', erw eq_mul, rw ← mul_eq_mul,
        ext, simp,
  end }
def image_equiv (ρ : group_representation G R M) (f : M ≃ₗ[R] M') :  ρ ≃ᵣ (image ρ f) := { ℓ := f,
  commute := begin 
        intros g, ext, unfold image, simp,
  end }
-/
end equiv_morphism
#lint