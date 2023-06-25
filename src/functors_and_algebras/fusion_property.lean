import category
import functors
import functors_and_algebras.tools
import functors_and_algebras.algebra_category
namespace category_theory

-- The fusion property states that given An initial F-algebra A and F-algebra B,
-- if we provide a morphism f : from B to another F-algebra C, then we can prove that 
-- if f makes this diagram commute: 
--              φ
--       𝔽(B)   →   B
--
--   F(f) ↓         ↓ (f)
--
--       F(C)   →   C
--              ψ
-- then composing the catamorphism from A to B with f results in the catamorphism from A to C.
def fusion {ℂ : category} {F : functor ℂ ℂ} (A : initial (AlgebraCategory F)) (B C : Falgebra F) (f : ℂ.hom B.object C.object) 
(square_proof : ℂ.compose f B.function = ℂ.compose C.function (F.map_hom f)) : ℂ.compose f (A.exist_morph B).morph = (A.exist_morph C).morph :=
begin
  -- We can utilize the Algebra category's composition of Homomorphisms to create one from A to C.
  -- Then, we apply the fact that A is an initial object and it's morphism is unique.
  have h := A.is_unique ((AlgebraCategory F).compose {morph := f, square_proof:= square_proof} (A.exist_morph B)),
  -- Since the 2 homomorphisms are equal, this implies that the underlying morphisms are also equal.
  cases (A.exist_morph C),
  cases h,
  simp [h],
end

end category_theory