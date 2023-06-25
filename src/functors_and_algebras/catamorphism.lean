import category
import functors
import functors_and_algebras.tools
import functors_and_algebras.algebra_category
import instances.Falgebras.initial_list_algebra

namespace category_theory

-- A catamorphism is a unique morphism ∎ψ∎ 
-- from an initial F-Algebra to another F-algebra with morphism ψ : 𝔽 (Y) → Y
--              φ
--       𝔽(X)   →   X
--
--   F(∎ψ∎) ↓         ↓ ∎ψ∎
--
--       F(Y)   →   Y
--              ψ

-- The lemma below states that a catamophism can be presented as a composition of
-- The morphism of a target algebra, the functor's mapping of the catamorphism itself, the inverse of φ.
lemma catamorphic_recursion {C : category} {F : functor C C} (A : initial (AlgebraCategory F)) (B : Falgebra F) :
∀ (iso : isomorphism A.object.function) , ((A.exist_morph B).morph = C.compose B.function (C.compose (F.map_hom (A.exist_morph B).morph) iso.inverse)) :=
  begin
    intros,
    -- For this proof we can use the fact that the catamorphism commutes the square diagram to algebra B.
    -- To use this, we first rewrite the nested Composition using C's associativity property.
    have h1 : C.compose B.function (C.compose (F.map_hom (A.exist_morph B).morph) iso.inverse) =
    C.compose (C.compose B.function  (F.map_hom (A.exist_morph B).morph)) iso.inverse := by simp [C.assoc],
    rw h1,
    -- Rewrite using the "square" diagram.
    simp [←(A.exist_morph B).square_proof],
    -- We can now use the fact that φ is an isomorphism to form the identity morphism.
    -- To do that, we rewrite the right-hand side using C's associativity.
    have h2 : C.compose (C.compose (A.exist_morph B).morph A.object.function) iso.inverse =
    C.compose  (A.exist_morph B).morph (C.compose A.object.function iso.inverse) := by simp [C.assoc],
    rw h2,
    -- Now, we can rewrite composition to Id, using the isomorphism property.
    have h3 : C.compose A.object.function iso.inverse = C.id A.object.object := by simp [iso.idl],
    rw h3,
    -- Now we can apply the fact that f ∘ Id = f in category C.
    simp [C.left_id],
  end

end category_theory