import category
import functors
import functors_and_algebras.f_algebra

open category_theory

-- The category of Algebras defined by a given functor 𝔽
def AlgebraCategory {C : category} (F : functor C C) : category := {
  -- Objects are Algebras defined by 𝔽 
  C₀  := Falgebra F,
  -- Morphisms in this category are Homomorphisms between two Algebras.
  hom :=λ A B, Fhomomorphism A B,
  -- The identity morphism in the category has 2 parts:
  -- 1) The morphism in category C, which is the id morphism of the category.
  -- 2) A proof that the diagram of the morphism commutes. We can prove that
  -- the 2 sides of the equality are the same by utilizing the fact that 
  -- 𝔽 preserves the id morphism, which leaves us with simply:
  -- C.compose (C.id A.object) A.function = C.compose A.function (C.id A.object),
  -- which we prove by using the left and right identity properties of category C.
  id := λ A, {
    morph := C.id A.object,
    square_proof := by simp [F.id, C.right_id, C.left_id],
  },
  -- Composition of the underlying morphisms is achieved by the composition of category C.
  -- To prove that the composed morphism is now in the form presented below, we will provide a step by step explanation:
  --                φ
  --         𝔽(X)   →   X
  --
  --   F(g∘f) ↓         ↓ (g∘f)
  --
  --         F(Z)   →   Z
  --                ψ
  compose := λ X Y Z g f,
    {
      morph := C.compose g.morph f.morph,
      square_proof :=
      begin 
        -- We will first transform the left-hand side of the equation
        -- Apply the Associativity property of Category C - (g ∘ f) ∘ ψ = g ∘ (f ∘ ψ)
        have h :  C.compose (C.compose g.morph f.morph) X.function 
        = C.compose g.morph (C.compose f.morph X.function) := by simp [C.assoc],
        simp [h],
        -- Now we can apply the fact that f's square commutes
        have h1 : C.compose f.morph (X.function) 
        = C.compose Y.function (F.map_hom f.morph) := by simp [f.square_proof],
        simp [h1],
        -- We revert the composition associativity
        have h2 : C.compose g.morph (C.compose Y.function (F.map_hom f.morph))
        = C.compose (C.compose g.morph Y.function) (F.map_hom f.morph) := by simp [C.assoc],
        simp [h2],
        -- Now we apply the fact that g's square commutes
        have h3 : C.compose g.morph (Y.function) 
        = C.compose Z.function (F.map_hom g.morph) := by apply g.square_proof,
        simp [h3],
        -- We apply the composition associativity, again
        have h4 : C.compose (C.compose Z.function (F.map_hom g.morph)) (F.map_hom f.morph)
        = C.compose Z.function (C.compose (F.map_hom g.morph) (F.map_hom f.morph)) := by simp [C.assoc],
        simp [h4],
        -- Now we apply Functor's preservation of composition
        have h5 : C.compose (F.map_hom g.morph) (F.map_hom f.morph) 
        = F.map_hom (C.compose g.morph f.morph) := by simp [F.comp],
        simp [h5],
      end,
    },
  -- To prove the left identity property, we rely on the same property of category C for the morphism.#check
  -- To prove the equality of the resulting square, Lean identifies that the 2 morphisms are equal, thus the proofs are equal as well.
  left_id :=
  begin
    intros X Y f,
    simp [C.left_id],
    cases f,
    have h : f_square_proof = _ := by refl,
    simp [h]
  end,
  -- The proof of right identity is the same as the left identity one.
  right_id := 
  begin
    intros X Y f,
    simp [C.right_id],
    cases f,
    have h : f_square_proof = _ := by refl,
    simp [h]
  end,
  -- Associativity of Homomorphisms can be proven by 
  -- simply using the associativity propery of underlying morphisms.
  assoc :=
  begin
    intros _ _ _ _ f g h,
    simp [C.assoc],
  end,
}