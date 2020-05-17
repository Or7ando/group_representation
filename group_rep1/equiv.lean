import linear_algebra.basic   
import algebra.module  
variables (M : Type )(R :Type) [ring R] [add_comm_group M]  [add_comm_group M] [module R M]
variables (f g : M→ₗ[R]M)
example : f * g = linear_map.id := sorry

#check (by apply_instance : has_mul (M→ₗ[R]M ))

linear_map.has_scalar