import category
import functors

namespace category_theory

-- An F-Algebra contains an object 𝔸 and a morphism φ : 𝔽 (𝔸) → 𝔸
structure Falgebra {C : category} (F : functor C C):=
  (object : C.C₀)
  (function : C.hom (F.map_obj object) object)

-- Given two F-Algebras (X, φ) and (Y, ψ),
-- A morphism f : X → Y is an F-Algebra homomorphism if the following diagram commutes:
--              φ
--       𝔽(X)   →   X
--
--   F(f) ↓         ↓ (f)
--
--       F(Y)   →   Y
--              ψ
structure Fhomomorphism {C : category} {F : functor C C} (A B : Falgebra F) :=
  (morph : C.hom A.object B.object)
  (square_proof : 
    C.compose morph (A.function) = C.compose B.function (F.map_hom morph))  


end category_theory