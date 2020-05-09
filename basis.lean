import linear_algebra.basic
import linear_algebra.basis
import algebra.big_operators
universes u v w
variables (X : Type u)(R : Type v)[comm_ring R][decidable_eq X][fintype X]

def ε (x : X) : (X → R) := λ y, if x = y then 1 else 0
variables ( x y : X)
#check ε X R x 

lemma  test1 (g : X → R)(s : finset X) : (λ (i : X), g i • ε X R i y)  = λ (i : X), if y = i then g y else 0 := begin 
    funext,
    split_ifs, unfold ε, split_ifs,rw h, change g i * 1 = _, rw mul_one, have hypo : i = y, rw h, trivial,
    unfold ε,split_ifs, change (g i) * 1 = _, rw mul_one, have hyp : y= i, rw h_1, trivial, change (g i) * 0 = 0, rw mul_zero, 
end
#check finset.sum_ite_eq 
lemma  test  (g : X → R)(s : finset X)(y ∈  s) : finset.sum s ((λ (i : X), g i • ε X R i) ) y = g y := 
begin 
    rw finset.sum_apply,
    erw test1, 
    rw finset.sum_ite_eq,split_ifs, exact rfl,
    assumption,
end
lemma rtrt  (g : X → R)(s : finset X)(y ∈  s) : finset.sum s ((λ (i : X), g i • ε X R i) ) y =  finset.sum s ((λ (i : X), g i • ε X R i y) ) :=
begin 
    rw finset.sum_apply, exact rfl,
end
lemma trr (M : Type w)[add_comm_group M][module R M] (p : submodule R M)(g : X → M) : set.range g ⊆ p  → finset.sum finset.univ g ∈ p :=
 begin   
    sorry,
 end
lemma gen (g : X → R) : g = finset.sum (finset.univ) (λ (x : X), g x • ε X R x) := 
begin 
    funext, rw finset.sum_apply, 
    change g x = finset.sum finset.univ (λ (g_1 : X), (g g_1 • ε X R g_1 x) ),
    rw test1,rw finset.sum_ite_eq,split_ifs,exact rfl,
    have R : x ∈ finset.univ, exact finset.mem_univ x, trivial,
    use finset.univ,
end
theorem classical_basis : is_basis R (ε X R) := 
begin 
    split,
    {
        rw linear_independent_iff', intros s, intros g,
        intros hyp,
        intros y, intro hyp_y,
        rw function.funext_iff at hyp,
        specialize hyp y,
        rw test at hyp, exact hyp, assumption,
        },
    { rw eq_top_iff, rw submodule.le_def',
    intros g, intros hyp, rw submodule.mem_span,
    intros p, intros hyp',
    let F := gen X R g, rw F, 
    let G := trr X R (X → R) p (λ (x : X), g x • ε X R x),
    apply G,
    rw set.subset_def, 
    intros g, intros hyp, rw set.mem_range at hyp,
    rcases hyp with ⟨y,hyp_rang ⟩,
    rw ← hyp_rang,  
    apply submodule.smul,
    rw [set.subset_def] at hyp',
    specialize hyp' (ε  X R y),
     have GGGG : ε X R y ∈ set.range (ε X R),
        exact set.mem_range_self  y,
        exact hyp' GGGG,
    },
end 
