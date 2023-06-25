import .category

namespace category_theory

def is_mono {C : category} {X Y Z : C} (f : C.hom X Y) :=
  ∀ {g₁ g₂ : C.hom Z X}, C.compose f g₁ = C.compose f g₂ → g₁ = g₂

def is_epic {C : category} {X Y Z : C} (f : C.hom X Y) :=
  ∀ {g₁ g₂ : C.hom Y Z}, C.compose g₁ f = C.compose g₂ f → g₁ = g₂

def is_iso {C : category} {X Y : C} (f : C.hom X Y) :=
  ∃ (g : C.hom Y X),((C.compose g f) = (C.id X)) ∧ ((C.compose f g) = (C.id Y))

def section_retraction_pair {C : category} {X Y : C} (s : C.hom X Y) (r : C.hom Y X) :=
  C.compose r s = C.id X

end category_theory
