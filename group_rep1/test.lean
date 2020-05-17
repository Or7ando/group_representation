import tactic

variables (ℓ : Type) (B : Prop) (C : ℓ → Prop)

def axiom_5: (∀ x : ℓ , B → C x) → (B → (∀ x : ℓ , C x)) :=
begin
  finish,
end