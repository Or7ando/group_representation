import .group_representation
import linear_algebra.determinant
import linear_algebra.matrix
import data.complex.basic
open linear_map
notation `Σ` := finset.sum finset.univ 
universe variables u v w 
open matrix
namespace character
variables {G : Type u} {R : Type v} [group G] [comm_ring R] 
variables {n : Type w} [fintype n] [decidable_eq n] 
variables (ρ : group_representation G R (n → R)) 
def mat (ρ : group_representation G R (n → R))(g : G) : matrix n n R :=
                 to_matrix (ρ g : (n → R) →ₗ[R] (n→ R)) 
namespace tools

/- 
     Technical 
     C'est vraiment trop leger ! 
-/
lemma proof_strategy (A B : matrix n n R) : to_lin A = to_lin B → A = B := begin 
     intro hyp,
     have RR : to_matrix (to_lin A) = to_matrix (to_lin B),
          congr',
     iterate 2 {rw  to_lin_to_matrix  at RR},
     exact RR,   
end
@[simp]lemma mat_ext (ρ : group_representation G R (n → R))(g : G) : mat ρ = λ g, to_matrix (ρ g : (n → R) →ₗ[R] (n→ R))  := rfl
lemma coersion₇ (g1 g2 : G) : (↑(ρ g1 * ρ g2) : (n → R) →ₗ[R] (n→ R)) = (ρ g1 :  (n → R) →ₗ[R] (n→ R) ) *  ρ g2  := rfl

@[simp]lemma  mat_mul' (g1 g2 : G) : 
to_matrix (ρ (g1 * g2) : (n → R) →ₗ[R] (n→ R) ) = 
to_matrix (ρ g1 : (n → R) →ₗ[R] (n→ R)) *  to_matrix (ρ g2) := begin 
    rw ρ.map_mul, rw  coersion₇, apply proof_strategy, rw mul_eq_mul,
     rw mul_to_lin, rw to_matrix_to_lin, rw to_matrix_to_lin, rw to_matrix_to_lin, exact rfl,
end 
end tools
open tools 
#check  mat ρ 
def χ  : G →  R :=  λ g, matrix.trace n R R (mat ρ g)

lemma chi_apply (g : G) : χ ρ g = matrix.trace n R R (mat ρ g) := rfl 
#check χ ρ  
variables (g : G)
#check χ ρ 

@[simp]lemma mat_mul (g1 g2 : G) : mat ρ (g1 * g2)  = mat ρ g1 * mat ρ g2 := begin 
    exact mat_mul' ρ g1 g2,
end
def   trace_mul_com (A B : matrix n n R)  :  matrix.trace n R R (A * B) = matrix.trace n R R (B *A)  :=  
 begin rw mul_eq_mul,rw trace_mul_comm, rw ← mul_eq_mul, end  --homotopy 


@[simp]theorem χ_is_central ( s t : G) : χ ρ (s * t) = χ ρ (t *  s ):= 
begin 
    rw chi_apply,rw chi_apply, rw mat_mul, rw trace_mul_com, rw ← mat_mul,
 end 

@[simp]theorem χ_is_constante_on_conjugacy_classes ( s t : G) : χ ρ ( t⁻¹ * s * t) = χ ρ (  s ):= begin 
    rw χ_is_central, rw ← mul_assoc, rw mul_inv_self, rw one_mul,
end
@[simp]lemma to_matrix_one : to_matrix (↑(ρ 1 ) : (n → R) →ₗ[R] (n→ R) ) = 1 := begin 
     rw ρ.map_one,
     apply proof_strategy,
     rw to_matrix_to_lin,
     rw to_lin_one, exact rfl,   --- there is not this function in mathlib 
end
@[simp]lemma mat_one : mat ρ 1 = 1 := to_matrix_one ρ 
@[simp]lemma mat_mul_inv_self (g : G) : mat ρ g * mat ρ g⁻¹ = 1 := begin rw ← mat_mul,rw mul_inv_self, rw mat_one, end
@[simp]theorem χ_one : χ ρ 1 =  fintype.card n := begin 
     rw chi_apply, rw mat_one, rw trace_one,
end
end character 
section 
variables {G :Type u} (R : Type v) [group G] [comm_ring R][fintype G][decidable_eq G]
def central_function  (f : G → R) :=  ∀ s t : G, f (s * t) = f (t * s)
lemma central (f : G → R)[hyp : central_function   R f] (s t : G) :  f (s * t) = f (t * s) := hyp s t 

theorem central_function_are_constant_on_conujugacy_classses (f : G → R)[hyp : central_function  R f] 
               : ∀ s t : G, f (t⁻¹ * s * t) =  f s :=
begin 
    intros s t, rw hyp,rw ← mul_assoc, rw mul_inv_self, rw one_mul,
end
notation  `inv` G  := ((1 / fintype.card G) : ℂ )
noncomputable def scalar_product   (φ ψ : G → ℂ  ) :=
       (inv G)   * (Σ  (λ t : G, (φ t) *  (complex.conj (ψ t))))     

variables (φ ψ :  G → ℂ  )
notation `《 ` φ ` | ` ψ ` 》` := scalar_product φ ψ 
/--
     `《 φ + γ | ψ 》 = 《 φ | ψ 》 + 《 γ  | ψ 》`
-/
theorem add_first  (φ ψ γ  : G → ℂ  ) : 《 φ + γ | ψ 》 = 《 φ | ψ 》 + 《 γ  | ψ 》 := 
begin 
      unfold scalar_product,rw ← left_distrib, erw ← multiset.sum_map_add,
     have f : (λ (a : G), φ a * complex.conj (ψ a) + γ a * complex.conj (ψ a)) = (λ (a : G), (φ a  + γ a ) * complex.conj (ψ a)),
          funext,
          rw ← right_distrib,
     erw f,
     exact rfl,
end
/--
     `《 r • φ  | ψ 》 = r • 《 φ | ψ 》`
-/
theorem smul_first  (r : ℂ) (φ ψ   : G → ℂ  ) : 《 r • φ  | ψ 》 = r • 《 φ | ψ 》 := begin 
      unfold scalar_product, 
      change 1 / ↑(fintype.card G) * Σ (λ (t : G), r * (φ t) * complex.conj (ψ t)) = _,
      have re : (λ (t : G), r * (φ t) * complex.conj (ψ t)) =  (λ (t : G), r •((φ t) * complex.conj (ψ t))),
          funext,
          rw mul_assoc, exact rfl,
     rw re,
     erw  ←  finset.mul_sum ,erw ← mul_assoc, erw mul_comm _ r , simp, rw mul_assoc,
end
lemma Sum.morp 
{X : Type u}[fintype X] (g : X → ℂ )  : complex.conj ( Σ (λ t,  g t )) =  Σ (λ t, complex.conj ( g t) )    := begin
    exact eq.symm (finset.sum_hom finset.univ complex.conj),
end
theorem conj_scalar (φ ψ   : G → ℂ  ) : complex.conj(《  φ  | ψ 》) = 《 ψ  | φ 》 := begin
     unfold scalar_product, rw complex.conj_mul,
     --have : complex.conj (Σ (λ (t : G), φ t * complex.conj (ψ t))) =   Σ (λ (t : G), complex.conj (φ t * complex.conj (ψ t))),
          erw Sum.morp,simp,
end 
#check is_add_monoid_hom (complex.conj)
end
