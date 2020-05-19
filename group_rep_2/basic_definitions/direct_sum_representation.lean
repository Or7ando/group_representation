import basic_definitions.group_representation
import linear_algebra.direct_sum_module
universes u v w u₁
variables (R : Type u) [ring R]
          (G : Type v)[group G]
          (ι : Type w) [decidable_eq ι] 
          (M : ι → Type w)
          [Π i, add_comm_group (M i)] 
          [Π i, module R (M i)] 
          (ρ  : Π i, group_representation G R (M i)) 
          
variables (i : ι ) (g : G) (x y : M i)
#check ρ i g (x+y)
example : ρ i g (x+y) = ρ i g (x) +ρ i g (y) := begin
    rw (ρ i g).map_add,
end
#check direct_sum ι M 
#check direct_sum.lof R ι  M i 
#check   direct_sum.to_module  R ι ( direct_sum ι  M ) (λ i,  (direct_sum.lof R ι  M i) ⊚ ( ρ i g))  
#check to_module_lof
open direct_sum
#check to_module_lof R i x 

def direct_sum_representation : group_representation G R (direct_sum ι M) :=
{ to_fun    := λ g, direct_sum.to_module  R ι ( direct_sum ι  M ) (λ i,  (direct_sum.lof R ι  M i) ⊚ ( ρ i g)),
  map_one'  := 
    begin 
    ext,let t :=  
    @to_module_lof R _  ι _ M _ _ (direct_sum ι M) _ _ (λ i,  (direct_sum.lof R ι  M i) ⊚ ( ρ i 1)) i (x i),
    let h := lof_apply R i (x i),
    
    end,
  map_mul'  := _ }
