import category

namespace category_theory

-- Given a category C:
-- Object A ∈ C₀ is initial if there is a unique morphism from A to every object B ∈ C₀
def is_initial (C : category) (A : C.C₀) : Prop :=
  ∀ (B : C.C₀) (f g : C.hom A B), f = g

structure initial_object (C : category) := 
  (object : C.C₀)
  (property : is_initial C object)


-- Given a category C:
-- Object B ∈ C₀ is terminal if there is a unique morphism from every object A ∈ C₀ to B
def is_terminal (C : category) (B : C.C₀) : Prop :=
  ∀ (A : C.C₀) (f g : C.hom A B), f = g

structure terminal_object (C : category) :=
  (object : C.C₀)
  (property : is_terminal C object)


-- Given category C and objects A, B ∈ C₀:
-- A triple (P, π₁: P ⟶ A, π₂: P ⟶ B) is called a product of A and B if
-- for any triple (Q, q₁: Q ⟶ A, q₂: Q ⟶ B) there is a unique morphism f: Q ⟶ P
-- such that π₁ ∘ f = q₁ and π₂ ∘ f = q₂
def is_binary_product (C : category) {A B : C.C₀} (P : C.C₀) (π₁ : C.hom P A) (π₂ : C.hom P B) : Prop :=
                        ∀ (Q : C.C₀) (q₁ : C.hom Q A) (q₂ : C.hom Q B),
                          ∃! (f : C.hom Q P), C.compose π₁ f = q₁ ∧ C.compose π₂ f = q₂

structure binary_product (C : category) (A B : C.C₀) :=
  (P : C.C₀)
  (π₁ : C.hom P A)
  (π₂ : C.hom P B)
  (property : is_binary_product C P π₁ π₂)


-- Given category C and objects A, B ∈ C₀:
-- A triple (Cₚ, ι₁: A ⟶ Cₚ, ι₂: B ⟶ Cₚ) is called a coproduct of A and B if
-- for any triple (D, i₁: A ⟶ D, i₂: B ⟶ D) there is a unique morphism f: Cₚ ⟶ D
-- such that f ∘ ι₁ = i₁ and f ∘ ι₂ = i₂
def is_binary_coproduct (C : category) {A B : C.C₀} (Cₚ : C.C₀) (ι₁ : C.hom A Cₚ) (ι₂ : C.hom B Cₚ) : Prop :=
                        ∀ (D : C.C₀) (i₁ : C.hom A D) (i₂ : C.hom B D),
                          ∃! (f : C.hom Cₚ D), C.compose f ι₁ = i₁ ∧ C.compose f ι₂ = i₂
 
structure binary_coproduct (C : category) (A B : C.C₀) :=
  (Cₚ : C.C₀)
  (ι₁ : C.hom A Cₚ)
  (ι₂ : C.hom B Cₚ)
  (property : is_binary_coproduct C Cₚ ι₁ ι₂)

end category_theory