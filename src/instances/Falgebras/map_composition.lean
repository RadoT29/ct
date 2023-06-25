import instances.Set_category
import functors_and_algebras.tools
import instances.Falgebras.initial_list_algebra
import functors_and_algebras.fusion_property

open category_theory

-- Definition of map as a fold
def map {A B : Set.C₀} (f : Set.hom A B) : Set.hom (List A) (List B) :=
  fold (List_fun (λ _, List.nil) (λ p, List.cons (f (fst p)) (snd p)))

-- The map algebra, defined by the function, which the fold inside the map function utilizes. 
def map_algebra {A B : Set.C₀} (f : Set.hom A B):
 Falgebra (list_algebra_functor A) :=
{
  object := List B,
  function := List_fun (λ _, List.nil) (λ p, List.cons (f (fst p)) (snd p))
}

-- Proof that map is a homomorphism from the map algebra of function f to the composed algebra of g and f
def hom_map_alg {A B C: Set.C₀} (f : Set.hom A B) (g : Set.hom B C) : 
  Fhomomorphism (map_algebra f)  (map_algebra (Set.compose g f)) := {
    morph := map g,
    -- Lean is able to help us with the commuting proof, since the composition in the category of sets
    -- is defined by ∘ , which is built-in and automated. 
    square_proof :=
    begin
      apply funext,
      intro l,
      cases l,
      case Either.left {
        refl,
      },
      case Either.right : p {
        refl,
      },
    end,
  }

-- Proof that (map g) ∘ (map f) = map (g ∘ f), using the fusion property
def map_composition {A B C: Set.C₀} : ∀ (f : Set.hom A B) (g : Set.hom B C), 
  Set.compose (map g) (map f) = map (Set.compose g f) := 
  begin
    intros,
    -- Lemma stating the fusion property. However, before applying it to the goal, we need to 
    -- prove that map f is the catamorphism to the map f algebra
    -- and that map (g ∘ f) is the catamorphism to the map (g∘f) algebra.
    have h1 := fusion (initial_list_algebra_proof A) (map_algebra f) (map_algebra (Set.compose g f)) (hom_map_alg f g).morph (hom_map_alg f g).square_proof,
    -- By definition of the homomorphism between the (map g) algebra and the (map g ∘ f) algebra,
    -- we can rewrite map g as the morphism of the unique catamorphism.
    have h2 : (hom_map_alg f g).morph = map g := by refl,
    rw ←h2,
    -- By the definition of map (which uses fold φ, where φ is the 𝔽(X) → X morphism of the (map f) algebra),
    -- we can state that map f is the catamorphism to that algebra.
    have h3 : ((initial_list_algebra_proof A).exist_morph (map_algebra f)).morph = map f := by refl,
    rw ←h3,
    -- Similarly, we can state that map (g ∘ f) is the catamorphism to the (map g ∘ f) algebra.
    have h5 : ((initial_list_algebra_proof A).exist_morph (map_algebra (Set.compose g f))).morph = map (Set.compose g f) := by refl,  
    rw ←h5,
    -- Currently, we have rewritten all maps as catamorphisms (that Lean can understand), thus 
    -- we can apply the fusion property to complete the proof. 
    rw h1,
  end 