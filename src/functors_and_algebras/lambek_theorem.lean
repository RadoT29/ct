import category
import functors
import morphisms
import functors_and_algebras.f_algebra
import functors_and_algebras.tools
import functors_and_algebras.fusion_property
import functors_and_algebras.algebra_category

namespace category_theory

-- The algebra, which maps both the object and the morphism of another algebra by the functor 𝔽
def algebra_f {C : category} {F : functor C C} (alg : Falgebra F) : Falgebra F := {
  object := F.map_obj alg.object,
  function := (F.map_hom alg.function),
}

-- Lambek's theorem states that the function in an initial algebra
-- 1) is an isomorphims
-- 2) its inverse is the catamoprhism to the algebra above.
-- A more visual example:
--        φ
--        →
-- 𝔽 (𝔸)     𝔸
--        ←
--     ∎F(φ)∎
def lambek_theorem {C : category} {F : functor C C} (algebra : initial (AlgebraCategory F))
  : ∀ iso : isomorphism algebra.object.function, iso.inverse = (algebra.exist_morph (algebra_f algebra.object)).morph :=
begin
  intros,
  -- In order to prove that every isomorphism's inverse is equal to the catamorphism to the algebra with object 𝔽(X)
  -- we will construct an isomorphism of φ, where the inverse is the catemorphism and 
  -- we will utilize the uniqueness property of an isomorphism.
  have h1 := inverse_uniqueness algebra.object.function iso {
    -- Construction of the isomorphism, using the X → 𝔽(X) morphism
    inverse := (algebra.exist_morph (algebra_f algebra.object)).morph,
    -- Proof that C.compose (𝔽(X) → X) (X → 𝔽(X)) = C.id X
    idl :=
    begin
      -- We use the fusion property, in order to prove that the composition (𝔽(X) → X) ∘ (X → 𝔽(X))
      -- is the same as the catamorphism from the initial algebra, back to itself.
      have h1 := fusion algebra (algebra_f algebra.object) algebra.object algebra.object.function,
      -- Proof that φ commutes the square diagram.
      have h2 : C.compose algebra.object.function (algebra_f algebra.object).function =
        C.compose algebra.object.function (F.map_hom algebra.object.function) := by refl,
      -- We apply the commuting proof to the fustion property, in order to show that φ is a homomorphism.
      simp [h1 h2],
      -- Proof that the identity morphism of category C is also a homomorphism in the category of algebras.
      -- This is done by proving that it commutes the diagram from the initial algebra back to itself.
      have h3 : C.compose (C.id algebra.object.object) algebra.object.function = C.compose algebra.object.function (F.map_hom (C.id algebra.object.object)) := 
      begin
        -- The proof uses the fact that Id ∘ f = f
        simp [C.right_id],
        -- Apply the fact that 𝔽(Id_x) = Id_𝔽(x)
        simp [F.id],
        -- Apply the fact that f ∘ Id = f
        simp [C.left_id],
      end,
      -- Apply the uniqueness property of the catamorphism from the initial algebra back to itself.
      -- This way, we prove that the identity homomorphism is indeed the unique catamorphism.
      have h4 := algebra.is_unique {morph := (C.id algebra.object.object), square_proof := h3},
      simp [←h4], 
    end,
    -- Proof that C.compose (X → 𝔽(X)) (𝔽(X) → X) = C.id 𝔽(X)
    idr :=
    begin
      -- This proof is the same as the one from C.id X, but both sides are wrapped by 𝔽().
      -- To show this, we first apply the fact that the catamorphism to the algebra with object 𝔽(X), commutes it's square diagram.
      -- Thus, we can represent the left-hand side with the other 'path' to 𝔽(X). 
      simp [(algebra.exist_morph (algebra_f algebra.object)).square_proof],
      -- In this part we prove that we can rewrite the 2 sides of the equation as mapped by 𝔽.
      have h1 : (algebra_f algebra.object).function = F.map_hom algebra.object.function := by refl,
      rw h1,
      simp [←F.comp],
      simp [←F.id],
      -- The rest of the proof is identical to the one for C.id, which is explained above.
      have h1 := fusion algebra (algebra_f algebra.object) algebra.object algebra.object.function,
      have h2 : C.compose algebra.object.function (algebra_f algebra.object).function =
        C.compose algebra.object.function (F.map_hom algebra.object.function) := by refl,
      simp [h1 h2],
      have h3 : C.compose (C.id algebra.object.object) algebra.object.function = C.compose algebra.object.function (F.map_hom (C.id algebra.object.object)) := 
      begin
        simp [C.right_id],
        simp [F.id],
        simp [C.left_id],
      end,
      have h4 := algebra.is_unique {morph := (C.id algebra.object.object), square_proof := h3},
      simp [←h4], 
    end,
  },
  simp [h1],
end

end category_theory