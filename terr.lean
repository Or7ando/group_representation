import category_theory.category

open category_theory
universes v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

local notation f `# ` A ` #` g := (f : _ ⟶ A) ≫ g

example {P Q R S : C} (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S) : f ≫ g ≫ h = ((f ≫ g) ≫ h) :=
begin

end