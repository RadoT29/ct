import instances.Set_category
import functors_and_algebras.bin_tree_functor
import functors_and_algebras.f_algebra
import functors_and_algebras.tools
import functors_and_algebras.algebra_category

open category_theory
open category_theory.BTree

-- The algebra of the 𝔸 + (X × X) functor, where the object is a binary tree.
def bin_tree_algebra {A : Set.C₀} : Falgebra (bin_tree_algebra_functor A) := {
  -- The object is a binary tree.
  object := BTree A,
  -- Mapping 𝔸 + (X × X) to a Binary tree is done by:
  -- 1) 𝔸 is mapped to leaf (𝔸)
  -- 2) (X × X) is mapped to node X X, we can imagine the 2 elements of the product
  -- as the branches of a tree node.  
  function := 
  begin
    intro F,
    cases F,
    case Either.left : a {
      exact leaf a,
    },
    case Either.right : p {
      exact node (fst p) (snd p),
    },
  end,
}

-- Construction of the universal homomorphism from the Algebra with object binary tree, to any algebra of the 𝔸 + (X × X) endofunctor
def bin_tree_hom {A : Set.C₀} (to : Falgebra (bin_tree_algebra_functor A)) : Fhomomorphism bin_tree_algebra to := {
  -- The morphism utilized the function of the other algebra, since this is a catamorphism.
  -- We can map the binary tree structure back to the form 𝔸 + (X × X) in order to have a compatible type.
  morph:= 
    begin
      intro x,
      induction x,
      case leaf : a {
        exact to.function (Either.left a),
      },
      -- Induction is used since, binary tree uses a recursive definition.
      case node : l r ihl ihr {
        exact to.function (Either.right ⟨ihl, ihr⟩),
      },
    end,
  -- Now we need to prove that the morphism commutes the diagram :
  --                    φ
  --      𝔸 + (X × X)   →   X
  --
  --   F(∎ψ∎) ↓             ↓ ∎ψ∎
  --
  --      𝔸 + (Y × Y)   →   Y
  --                    ψ
  -- This is a simple proof, since we know how the morphism utilizes ψ.
  -- Lean is able to alleviate the work on this proof, because The Set category utilizes 
  -- built-in features and we have defined the morphism directly during construction of the homomorphism,
  -- so Lean can automate the proof. 
  -- For a more detailed explanation, one can inspect the proof of why fold is a catamorphism for the categoty of algebras, defined by the 1 + (𝔸 × X) functor.
  square_proof:= 
    begin
      simp,
      apply funext,
      intro x,
      cases x,
      case Either.left : a {
        refl,
      },
      case Either.right : p {
        refl,
      },
    end,
}

-- Proof of the initiality of the algebra defined by the 𝔸 + (X × X) functor with binary tree as object. 
def bin_tree_algebra_initial_proof {A : Set.C₀} : initial (AlgebraCategory (bin_tree_algebra_functor A)) := {
  -- The initial object is the binary tree algebra, defined above
  object := bin_tree_algebra,
  -- The catamorphism of the algebra is defined by the homomorhpsim, which uses the 𝔽(X) → X morphism of the target algebra
  exist_morph:= bin_tree_hom,
  -- To prove uniqueness of the homomorphism, it is required to show that any other homomorphism f, it is equal to `bin_tree_hom`
  is_unique:=
  begin
    intros,
    cases f,
    -- To prove that 2 homomorhpisms are equal, it is sufficient to show that the underlying morphisms are the same.
    have h : f_morph = (bin_tree_hom X).morph := 
    begin
      apply funext,
      intro x,
      -- A Binary tree is an inductive data type, thu a proof by induction is utilized.
      induction x,
      -- The base case of the proof covers the leaf of a tree.
      case leaf : a {
        -- For this proof we make use of the fact that the morphism commutes its square diagram.
        -- Initially we have that we apply the 2 morphisms to type X.
        -- In order to use the commuing property we need equation of the form f ∘ (𝔽(X) → X).
        -- We transform the input leaf into 𝔽(X) → X, since we know exactly how the binary tree algebra maps its input.
        have h1 : leaf a = bin_tree_algebra.function (Either.left a) := by refl,
        rw h1,
        -- We apply the fact that composition in the category of sets is the same as f (g x).
        have h2 : f_morph (bin_tree_algebra.function (Either.left a)) = 
        Set.compose f_morph bin_tree_algebra.function (Either.left a) := by refl,
        rw h2,
        -- Now we can rewrite the left-hand side of the equation using the commuting property.
        rw f_square_proof,
        -- In this part, the right-hand side is rewritten using the commuting property of the catamorphism.
        have h3 : (bin_tree_hom X).morph (bin_tree_algebra.function (Either.left a)) = 
        Set.compose (bin_tree_hom X).morph bin_tree_algebra.function (Either.left a) := by refl,
        rw h3,
        rw (bin_tree_hom X).square_proof,
        -- Now we only need to state that because 𝔽 does not apply morphism to 𝔸, we have the same lhs and rhs.
        -- Lean is able to automate this part of the proof, by looking at the definition of the functor.
        refl,
      },
      -- The inductive case covers a node with depth until a leaf = k+1, with inductive hypothesis about the left and right children with depth k.
      case node : l r lih rih {
        -- For the right-hand side We apply the definition of the catamorphism and how it treats a node as input.
        have h1 : (bin_tree_hom X).morph (node l r) 
        = X.function (Either.right ⟨(bin_tree_hom X).morph l, (bin_tree_hom X).morph r⟩):= by refl, 
        rw h1,
        -- The inductive hypothesis is now applied. Because a node consists of 2 children, we have 2 parts of the hyprotesis.
        rw [←lih, ←rih],
        -- Moving on to the left-hand side, X is transformed into 𝔽(X) → X the way it was done in the base case.
        have h2 : node l r = bin_tree_algebra.function (Either.right ⟨l, r⟩) := by refl,
        rw h2,
        -- Again, the we apply the Set composition (in reverse).
        have h3 : f_morph (bin_tree_algebra.function (Either.right ⟨l,r⟩)) = 
        Set.compose f_morph bin_tree_algebra.function (Either.right ⟨l,r⟩) := by refl,
        rw h3,
        -- Rewrite the lhs using the commuting property of the f homomorphism.
        rw f_square_proof,
        -- Lean is able to apply the morphism mapping of the functor and automate the proof.
        refl,
      }, 
    end,
    -- The catamorphism is split into elements, as lean is undable to rewrite the statement otherwide, and the proof above is applied.
    cases bin_tree_hom X,
    simp [h],
  end,
}