import instances.Set_category
import functors
import .tools

namespace category_theory

-- F𝔸 functor : X → 𝔸 + (X × X)
-- This functor can be used for a Binary Tree Algebra.
-- We can imagine that Leaf is 1 (i.e a singleton element) and X × X is a node with 2 children.
def bin_tree_algebra_functor (A : Set.C₀) : functor Set Set := {
  -- The functor maps objects from set A to 𝔸 + (X × X)
  map_obj:= λ X, Either A (Pair X X),
  -- Morphisms are applied only if the input is in the form (X × X).#check
  -- The morphism f is applied to both parts of the product.
  map_hom:= 
  begin
    intros X Y f x,
    cases x,
    case Either.left : l {
      exact Either.left l,
    },
    case Either.right : p {
      exact Either.right ⟨f (fst p), f (snd p)⟩
    },
  end,
  -- To prove that identity is preserved, we need to prove it for the 2 cases of the co-product.
  id:=
  begin
    intro,
    simp,
    apply funext,
    intro,
    cases x,
    -- Since no function is applied in the case of 𝔸, the input equals the output.
    case Either.left : l {
      refl,  
    },
    -- To prove the second case, we first show that applying ID in the Set category
    -- to the elements of the product results in no change to the elements.#check
    -- We then apply the fact that a product, which is constructed by the elements 
    -- of a product results in the product itself.
    case Either.right : p {
      simp,
      have h1 : ⟨Set.id X (fst p),Set.id X (snd p)⟩ = ⟨fst p, snd p⟩ := by refl,
      rw h1,
      simp [pair_eq],
      refl,
    },
  end,
  -- To prove composition, again we need to deal with 2 cases of the input.
  comp:= 
  begin
    intros,
    simp,
    apply funext,
    intro,
    cases x,
    -- Since no function is applied in the case of 𝔸, composition will not alter the input.
    case Either.left : l {
      refl,
    },
    -- It is enough to show that Composition of the elements of the product results in the 
    -- application of the 2 functions one after another in the category of sets.
    -- Lean is able to automate the end of the proof as it knows how 'map_hom' works by its definition. 
    case Either.right : p {
      simp,
      have h1 : ⟨Set.compose g f (fst p),Set.compose g f (snd p)⟩ = ⟨g (f (fst p)), g (f (snd p))⟩ := by refl,
      rw h1,
      refl,
    },
  end,
}

end category_theory