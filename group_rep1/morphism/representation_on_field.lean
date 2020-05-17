import morphism.projector
import linear_algebra.basis
universes  u v w w'
   
variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
[finite_dimensional K V](B : fin 3 → V)(hv : is_basis K B)
/-!
    Goal : For a sub-vector space `W ≤ V`, construction of a projector `p : V →ₗ[K] V`  with `range p = V`.
        Strategy : 
        we take a `basis of W` it a `linear_idependant familly of V`. We construct a `basis of V`
        witch complete. An we construct `p` on this basis 
-/
open is_basis linear_map
example {K : Type} {V : Type} [field K] [add_comm_group V] [vector_space K V]
[finite_dimensional K V](B : fin 3 → V)(hv : is_basis K B) : true := 
begin
    let φ := constr hv B,  --- construction d'une applocation linear sur une base !
    have R : φ  = linear_map.id,
         apply ext hv,   --- extension sur une base 
         intros,                                                                    
         rw linear_map.id_apply,   
         rw constr_basis,           --- expression sur la base de la construction !
        -- ici on va poser quelque question ? 
   -- have G :  (linear_map.range φ) = ⊤,
   --     change linear_map.range (is_basis.constr hv B) = ⊤,
   -- have f : nonempty (fin 3),
    --    use 1,
   -- rw @constr_range _ _ _ _ _ _ _  _ _  _  f hv ,
   let θ : fin 3 → V := λ a, if a ≤ 1 then (B a) else 0,
   let φ := constr hv θ,
   have R : linear_map.comp φ φ = φ ,
   apply is_basis.ext hv,
   intro i,
   rw comp_apply,
   rw constr_basis,
        sorry, 
   trivial,
 end
/-!
    Todo : matrice compagnon ... matrice cyclique matrice nilpotente ! etc. Y'a pas mal de chose a faire ! 
-/ 
variables (X : Type)[fintype X] [decidable_eq X] (x : X)
def Vr (x : X) :=  (λ i, std_basis K (λ i:X, K) i 1) x x    
#check (λ i, std_basis K (λ i:X, K) i 1)
#check exists_linear_independent 

lemma okok (x : X) :  (std_basis K (λ i:X, K) x 1) x = 1 := begin 
     exact std_basis_same K (λ i, K) x 1,
end

def ε {X : Type u}[fintype X] [decidable_eq X](K : Type v)[field K] : X → X → K := λ x, (std_basis K (λ i:X, K) x 1)

#check (ε K) 
def J : fin 3 → fin 3 := λ a, if a> 1 then 2 else 0
def classical_basis ( X : Type u)[fintype X][decidable_eq X](R : Type v)[comm_ring R] (x : X) : X → R := 
λ y : X, if x = y then 1 else 0

lemma obj ( X : Type u)[fintype X][decidable_eq X](R : Type v)[comm_ring R] (x : X) :  
classical_basis X R x x = 1 := begin 
    dsimp only [classical_basis]; split_ifs,
    exact rfl,
    exact rfl,
end

