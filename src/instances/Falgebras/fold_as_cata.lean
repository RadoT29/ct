import functors_and_algebras.catamorphism

open category_theory
-- In this file we will present an example the fold (the catamorphism in the category of list algebras) 
-- can be rewritten as recursive definition by the catamorphism property.

-- First, let's define the isomorphism of the 𝔽(X) → X morphism of the initial list algebra.
def list_iso {A : Set.C₀} : isomorphism (initial_list_algebra_proof A).object.function := {
  -- The inverse morphism can be defined as:
  -- 1) Nil is mapped back to ⋆
  -- 2) Cons hd tl is mapped to (𝔸 × X)
  inverse := 
  begin
    intro xs,
    cases xs,
    case List.nil {
      exact Either.left Singleton.star,
    },
    case List.cons : hd tl {
      exact Either.right ⟨hd, tl⟩,
    }, 
  end,
  -- Now we have to prove that (𝔽(X) → X) ∘ (X → 𝔽(X)) = Set.id X
  -- Since the definition of Set category uses built-in elements,
  -- Lean is able to automate the proof.
  idl :=
  begin
    simp,
    apply funext,
    intro xs,
    induction xs,
    case List.nil {
      refl,
    },
    case List.cons : hd tl ih {
      refl,
    },
  end,
  -- Proof that (X → 𝔽(X)) ∘ (𝔽(X) → X) = Set.id 𝔽(X)
  idr :=
  begin
    simp,
    apply funext,
    intro xs,
    cases xs,
    case Either.left : s {
      cases s,
      refl,
    },
    case Either.right : p {
      cases p,
      refl,
    },
  end,
}

-- Proof that fold can be recursively defined by the catamorphism property
-- Since we have already defined the isomorphism, we simply apply it to the catamorphism property lemma.
lemma fold_eq {A : Set.C₀} {B : Falgebra (list_algebra_functor A)} : fold B.function = 
  Set.compose B.function (Set.compose ((list_algebra_functor A).map_hom (fold B.function)) list_iso.inverse) :=
  begin
    exact catamorphic_recursion (initial_list_algebra_proof A) B list_iso,
  end 
