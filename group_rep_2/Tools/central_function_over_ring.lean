import data.fintype.basic
import linear_algebra.basic
universe variables u v 

variables {G :Type u} (R : Type v) [group G] 
/--
  A central fonction is a function `f : G → R` s.t  `∀ s t : G, f (s * t) = f (t * s)`
-/
def central_function  (f : G → R) :=  ∀ s t : G, f (s * t) = f (t * s)
lemma central (f : G → R)(hyp : central_function   R f) (s t : G) :  f (s * t) = f (t * s) := hyp s t 
/--
    A central function satisfy `∀ s t : G, f (t⁻¹ * s * t) =  f s`
-/
theorem central_function_are_constant_on_conjugacy_classses (f : G → R)(hyp : central_function  R f) 
               : ∀ s t : G, f (t⁻¹ * s * t) =  f s :=
begin 
    intros s t, rw hyp,rw ← mul_assoc, rw mul_inv_self, rw one_mul,
end
variables [comm_ring R]
/--
    We show that central function form a `free R-submodule` of `G → R` 
-/
def central_submodule : submodule R (G → R) := { 
    carrier := λ f, central_function R f,
    zero :=  begin unfold central_function, intros s t, exact rfl end,
    add := 
        begin 
            intros f g, intros hypf hypg, intros s t,
            change f _ + g _ = f _ + g _, erw hypf, erw hypg,
        end,
    smul := 
        begin 
            intros c, intros f, intros hyp, intros s t,
            change c • f _ = c • f _, rw hyp, 
        end 
}