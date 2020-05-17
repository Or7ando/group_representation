import linear_algebra.matrix
import Tools.matrix_tools
universe variables u v w t
open_locale big_operators matrix
open matrix linear_map
/--
    Technical : `ite (x0 = x ∧ y0 = y) (1 : R) 0 = (ite (x0 = x) 1 0) * (ite (y0 = y) 1 0)`
-/
@[simp]lemma mul_ite_ite  {X : Type u}[fintype X][decidable_eq X] {R : Type v} [comm_ring R]{Y : Type u} 
[fintype Y] [decidable_eq Y](x x0 : X) (y0 y : Y) : 
    ite (x0 = x ∧ y0 = y) (1 : R) 0 = (ite (x0 = x) 1 0) * (ite (y0 = y) 1 0) := 
begin
    split_ifs, 
        {rw mul_one}, 
        {rw h.2 at h_2, trivial},
        {rw h.1 at h_1,trivial},
        {rw h.1 at h_1,trivial}, 
        {rw [h_1,h_2] at h,push_neg at h,rcases h, {trivial}, {trivial}},
        {push_neg at h,rcases h,{trivial},{rw mul_zero}},
        {rw zero_mul},
        {rw zero_mul},
end
@[simp]lemma mul_ite_ite'{X : Type u}[fintype X][decidable_eq X] {R : Type v}  [comm_ring R]{Y : Type u} 
[fintype Y] [decidable_eq Y](x x0 : X) (y0 y : Y) : 
ite (  y0 = y ∧ x0 = x) (1 : R) 0 = (ite (x0 = x) 1 0) * (ite (y0 = y) 1 0) := 
begin
    rw ← mul_ite_ite, apply if_congr _ rfl rfl,exact and.comm,
end


variables {R : Type v}  [comm_ring R] 
          {X : Type u}[fintype X][decidable_eq X] 
          {Y : Type u}[fintype Y][decidable_eq Y]  -- same universe for matrix. 

/--
    Elementary matrix : for `(x0,y0) ∈ X × Y` : 
    `ℰ x0 y0 = λ x y, if x0 = x ∧ y0 = y then (1 : R) else 0`
-/
def ℰ : X → Y → X → Y → R := λ x0 y0 x y, if x0 = x ∧ y0 = y then (1 : R) else 0
/--
    Other expression of `ℰ`. 
-/
lemma E_eq : (ℰ : X → Y → X → Y → R) = λ x0 y0 x y, (ite (x0 = x) 1 0) * (ite (y0 = y) 1 0) 
:=  by ext; {erw ← mul_ite_ite, exact rfl} 
/--
    `Transposition` of the elementary matrix. 
    `transpose (ℰ x0 y0) = ℰ y0 x0`
-/
lemma E_transpose (x0 : X)(y0 : Y) : transpose (ℰ  x0 y0 : matrix X Y R) = ℰ y0 x0 :=
begin 
    ext, rw transpose_val,unfold ℰ , 
    rw mul_ite_ite,
    rw mul_ite_ite, 
    rw mul_comm, 
end
lemma E_transpose' (x0 : X)(y0 : Y) : transpose (ℰ x0 y0 : matrix X Y R) = ℰ y0 x0 :=
begin 
    ext, rw transpose_val,unfold ℰ , 
    apply if_congr _ rfl rfl, exact and.comm,
end
variables ( M : matrix X X R)
/--
    right multiplication by elementary matrix. 
    `M ⬝ ℰ x0 y0 = λ x y, if  y0 = y then M x x0 else 0`
-/
@[simp]lemma mul_E (x0 : X)(y0 : Y) : M ⬝ ℰ x0 y0  = λ x y, if  y0 = y then M x x0 else 0 := 
begin 
    ext x y, rw matrix.mul_val,
    unfold ℰ, simp  [-mul_ite_ite'], 
end

@[simp]lemma mul_E' (x0 : X)(y0 : Y) : M ⬝ ℰ x0 y0  = λ x y, if  y0 = y then M x x0 else 0 := 
begin 
    ext x y, rw mul_val,
    unfold ℰ, 
    conv_lhs {
        apply_congr,skip,
        rw mul_ite_ite, rw ← mul_assoc, rw mul_ite _ (M x x_1) _ _ , rw mul_zero, rw mul_one,
        rw  ite_mul, rw zero_mul,
    },
    erw finset.sum_ite_eq,simp,
end
/--
     `M ⬝ ℰ x0 y0  = ∑ x, M x x0 • (ℰ x y0)`
-/
@[simp]lemma mul_E_sum (x0 : X)(y0 : Y) : M ⬝ ℰ x0 y0  = ∑ x, M x x0 • (ℰ x y0) := 
begin
    ext x y, rw mul_E, 
    unfold ℰ, simp  [-mul_ite_ite'],
end
/--
    left multiplication by elementary matrix. 
    `ℰ x0 y0  ⬝ M =  λ x y, if  x0 = x then M y0 y else 0 `
-/
@[simp]lemma E_mul (x0 : X)(y0 : Y) ( M : matrix Y Y R) : (ℰ x0 y0 : matrix X Y R) ⬝ M  = 
            λ x y, if  x0 = x then M y0 y else 0 := 
begin 
    ext x y, rw matrix.mul_val,
    unfold ℰ, simp,
end
@[simp]lemma E__mul_sum (x0 : X)(y0 : Y) ( M : matrix Y Y R):  (ℰ x0 y0 : matrix X Y R) ⬝ M 
=  ∑ y, M y0 y • ℰ  x0 y := 
begin 
ext, rw E_mul,unfold ℰ, simp,
end
/--
    middle multiplication by elementary matrix. 
     `N ⬝ (ℰ x0 y0 ) ⬝ M = λ x y, N x x0 * M y0 y`
-/
@[simp]theorem mul_E_mul ( N : matrix X X R) (x0 : X)(y0 : Y) ( M : matrix Y Y R) :
 N ⬝ (ℰ x0 y0 ) ⬝ M = λ x y, N x x0 * M y0 y :=
begin 
    ext x y,rw mul_E, conv_lhs {
        apply_congr,skip,simp,
    },
    erw finset.sum_ite_eq,
    simp,
 end
theorem mul_E_mul' ( N : matrix X X R) ( x x0 : X)(y y0 : Y) ( M : matrix Y Y R) :
 (N ⬝ (ℰ x0 y0 ) ⬝ M) x y =  N x x0 * M y0 y :=
begin 
    rw mul_E_mul,
 end
lemma E_diag (y x: X) : ℰ y y x x = if x=y then (1 : R) else 0 := begin 
    unfold ℰ, split_ifs, {exact rfl},{finish},{finish},{exact rfl},
end  
lemma E_diag_ne ( y x a : X)(hyp : x ≠ y) : ℰ x y a a = (0 : R) := begin 
    unfold ℰ,split_ifs, {finish}, {exact rfl},
end
/--
    Trace of the elementary matrix :  `if x = y then 1 else 0`
-/
 lemma trace_E (x y : X) : matrix.trace X  R R (ℰ x y) = if x = y then (1 : R) else 0 := 
 begin 
    rw trace_value,
    split_ifs, rw h,  
    conv_lhs {
        apply_congr,skip, rw E_diag,
    },
    erw finset.sum_ite_eq',simp,
    conv_lhs {
        apply_congr,skip, rw E_diag_ne _ _ _ h,
    },
    simp,
 end

