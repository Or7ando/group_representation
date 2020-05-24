import linear_algebra.determinant
import linear_algebra.matrix
import Tools.tools
import basic_definitions.equiv
open linear_map matrix 
universe variables u v w  w'
open_locale big_operators
namespace character
variables {G : Type u} {R : Type v} [group G] [comm_ring R] 
variables {n : Type w} [fintype n] [decidable_eq n] 
variables (ρ : group_representation G R (n → R)) 


def mat (ρ : group_representation G R (n → R))(g : G) : matrix n n R :=
                 to_matrix (ρ g : (n → R) →ₗ[R] (n→ R)) 
namespace tools
/--
     Ici bof bof je pense ! c'est a refaire completement ! 
-/

@[simp]lemma mat_ext (ρ : group_representation G R (n → R))(g : G) : mat ρ = λ g, to_matrix (ρ g )  := rfl

@[simp]lemma  mat_mul' (g1 g2 : G) : 
to_matrix (ρ (g1 * g2)) =  to_matrix (ρ g1 ) *  to_matrix (ρ g2) := 
begin 
    rw map_comp, rw to_matrix_mul, exact rfl,
end 
end tools
open tools 
def χ  : G →  R :=  λ g, matrix.trace n R R (mat ρ g)

lemma chi_apply (g : G) : χ ρ g = matrix.trace n R R (mat ρ g) := rfl 

lemma chi_ext (g : G) : χ ρ g = ∑ i, (mat ρ g) i i := rfl


@[simp]lemma mat_mul (g1 g2 : G) : mat ρ (g1 * g2)  = mat ρ g1 * mat ρ g2 := 
tools.mat_mul' _ _ _


@[simp]theorem χ_is_central ( s t : G) : χ ρ (s * t) = χ ρ (t *  s ):= 
begin 
    rw chi_apply,rw chi_apply, rw mat_mul, erw matrix.trace_mul_comm,  erw  mat_mul, exact rfl,
 end 

@[simp]theorem χ_is_constante_on_conjugacy_classes ( s t : G) : χ ρ ( t⁻¹ * s * t) = χ ρ (  s ):= begin 
    rw χ_is_central, rw ← mul_assoc, rw mul_inv_self, rw one_mul,
end
@[simp]lemma to_matrix_one' : to_matrix ((ρ 1 ) : (n → R) →ₗ[R] (n→ R) ) = 1 := begin 
     rw ρ.map_one, exact to_matrix_one,
end
@[simp]lemma mat_one : mat ρ 1 = 1 := to_matrix_one' ρ 
@[simp]lemma mat_mul_inv_self (g : G) : mat ρ g * mat ρ g⁻¹ = 1 := 
begin rw ← mat_mul,rw mul_inv_self, rw mat_one, end
@[simp]theorem χ_one : χ ρ 1 =  fintype.card n := 
begin 
     rw chi_apply, rw mat_one, rw trace_one,
end
open_locale matrix 
/--
          ` trace  (mat ρ s⁻¹ ⬝ A ⬝ mat ρ s) = trace A`
-/
lemma  trace_conj (s : G) (A : matrix n n R)  : (matrix.trace n R R) (mat ρ s⁻¹ ⬝ A ⬝ mat ρ s) = matrix.trace n R R A := 
begin 
    erw matrix.trace_mul_comm, rw ← matrix.mul_assoc,
        rw ← matrix.mul_eq_mul, rw ← matrix.mul_eq_mul,
        rw ← character.mat_mul,
        rw mul_inv_self, rw character.mat_one,
        rw one_mul,
end
open equiv_morphism
variables  {Y : Type w}[fintype Y][decidable_eq Y] variables (ρ' : group_representation G R (Y → R))
end character 

namespace equivalence
open character
variables {G : Type u} {R : Type v} [group G] [comm_ring R] 
variables {X : Type w} [fintype X] [decidable_eq X]
variables  {Y : Type w}[fintype Y][decidable_eq Y] 
variables (ρ : group_representation G R (X → R))  
variables (ρ' : group_representation G R (Y → R))  
variables (φ : ρ  ≃ᵣ ρ' )

#check φ.ℓ.6
/-!
     DAns equiv il faut avoir des choses sur les ` * ` ici c'est trop faible 

-/
@[simp]lemma conjugaison (g : G) : (φ.ℓ.symm : (Y → R) →ₗ[R] (X → R))
 ⊚   (ρ' g : (Y → R) →ₗ[R] (Y → R) ) ⊚ 
     (φ.ℓ : (X → R) →ₗ[R] (Y → R)) = (ρ g : (X → R) →ₗ[R] (X → R)) := 
begin
     rw linear_map.comp_assoc,
     rw ← φ.commute,  rw ← linear_map.comp_assoc, ext,simp [φ.ℓ.5],
end
/--
     Ceci doit aller dans équiv ! 
-/
lemma inv_mul_self : (φ.ℓ.symm : (Y → R) →ₗ[R] (X → R)) ⊚  (φ.ℓ : (X → R) →ₗ[R] Y → R) = 1 := 
begin 
     ext,simp,
end 
lemma mul_inv_self :  (φ.ℓ : (X → R) →ₗ[R] Y → R) ⊚  (φ.ℓ.symm : (Y → R) →ₗ[R] (X → R)) = 1 := 
begin 
     ext,simp,
end  
lemma trace_ext (M : matrix Y Y R) : matrix.trace Y  R R M = ∑ i : Y, M i i := rfl
/--
     IL faut absolument refaire des fonctions du côté matrix !!! 
-/
theorem carac_eq (φ : ρ  ≃ᵣ ρ' )(g : G) : χ ρ g = χ ρ' g := 
begin
     rw chi_ext,
     rw tools.mat_ext, swap, by assumption,
     conv_lhs{
          apply_congr, skip,
          dsimp,erw ← conjugaison ρ ρ' φ,
     },
     erw ← trace_ext, erw to_matrix_trace_comm, 
     rw ← linear_map.comp_assoc,  rw mul_inv_self,
     erw linear_map.id_comp, rw  chi_apply, exact rfl,
end 
open equiv_morphism
--open_locale classical
theorem carac_eq' (hyp : is_isomorphic  ρ  ρ' ) : χ ρ  = χ ρ'  := 
begin
     funext g,
     rw chi_ext, unfold is_isomorphic at hyp,
     rcases hyp with φ, 
     rw tools.mat_ext, swap, by assumption,
     conv_lhs{
          apply_congr, skip,
          dsimp,erw ← conjugaison ρ ρ' φ,
     },
     erw ← trace_ext, erw to_matrix_trace_comm, 
     rw ← linear_map.comp_assoc,  rw mul_inv_self,
     erw linear_map.id_comp, rw  chi_apply, exact rfl,
end 
end equivalence
