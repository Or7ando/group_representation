import ring_theory.algebra
import ring_theory.ideals
/-!
    Galois algebra : B : Algebra A.    
    G →* Aut (B / A)
    est-ce que le groupe des automorphismes d'algebre est ok ! 
 `A →ₐ[R] B`
       
-/
namespace prio
variables (k : Type)[comm_ring k] (B : Type)[comm_ring B][algebra k B](G : Type)[group G][fintype G] [mul_action G B]

instance coe_base_to_algebra : has_coe(k)B := ⟨λ r, algebra_map k B r ⟩ 
end prio        
class Galois_algebra (k : Type)[comm_ring k] (B : Type)[comm_ring B][algebra k B](G : Type)[group G][fintype G] [mul_action G B]
 :=   
(G_mul' : ∀ g : G, ∀ x y : B, g • (x * y) = g • x * g • y)
(G_add' : ∀ g : G, ∀ x y : B, g • (x+y) = g • x + g • y)
(G_smul' : ∀ g : G, ∀ x : B, ∀ r : k, g • (r • x) = r • (g • x) )
(invariant' : ∀ b : B, ( (∀ g : G,  g •  b =  b) → (∃ a : k, b = a )))
/-!
*    ⟨ b - σ b | σ ∈ G ⟩ 
* 
-/ 
variables {k : Type}[comm_ring k] {B : Type}[comm_ring B][algebra k B]
{G : Type}[group G][fintype G] [mul_action G B]
[Galois_algebra k B G]   
#check Galois_algebra

example (g : G ) (b1 b2 : B):  g • (b1+b2) = g • (b1) + g • b2  := Galois_algebra.G_add'  
   
def 𝒥   : G → ideal B := λ g : G,  ideal.span $ set.image (λ b, b -  (g ⊚ b)) set.univ 

def separate_action (Δ : (Galois_algebra R B G)) : Prop := ∀ g : G, g ≠  1 → 𝒥  Δ  g  = ⊤ 


-- other has_mul_action ?  st g • (a * b)  = g • a * g • b, 