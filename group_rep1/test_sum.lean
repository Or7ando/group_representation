

universe variables u v w w'
open morphism
namespace morphism
variables {G : Type u} {R : Type v} [group G] [comm_ring R] 
variables [fintype G] [decidable_eq G] 
variables [ hyp : ∃ a : R,  a * fin_enum.card G = 1]
variables {M : Type w}  [add_comm_group M] [module R M]
          {M' : Type w'} [add_comm_group M'] [module R M'](n : Type) 
          {ρ : group_representation G R M} [finset n]
          {ρ' : group_representation G R M'}
#check (fin_enum.equiv G).inv_fun  
#check (fin_enum.equiv G).to_fun
#check (fin n)
#check finset.univ
#check fin_enum.fin. 
#check G → (M→ₗ[R]M') -- la representation m'offre ça je veux ∑ f (g)
#check n → R    --- sum G f 

#check  finset.sum (univ) g
variable (α : finset R)
#check finset
#check (set.image g : finset R)
#check finset.sum   
#check (range ((fin_enum.card G))).sum   
#check univ

variables (g : G → R)
#check Sum G g
notation    `Σ_ ` f := Sum f 
#check   Σ_  g 
variables (f :  G   → (M→ₗ[R]M'))
#check fine.numuniv (range (fin_enum.card (G))) 
variables (m : ℕ) 
#check (finset.range m)
def Reynold_operator  (f : M→ₗ[R]M') : ρ ⟶ ρ' := { ℓ := _,
  commute := _ }
finset.mul_sum, finset.sum_mul
end morphism 
variables {R : Type v}[ring R] (X : Type)[fin_enum X] (f : X → R) 



