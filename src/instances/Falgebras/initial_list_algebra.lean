import category
import instances.Set_category
import functors_and_algebras.tools
import functors_and_algebras.f_algebra
import functors_and_algebras.list_functor
import functors_and_algebras.algebra_category
import instances.functors.List_functor

open category_theory

-- Morphism 𝔽 (X) → X
-- This function provides an easy way to create a function for the algebra using the 1 + 𝔸 × X functor.
-- Given functions for the left and right cases we prove that this function is an instance of one for the desired functor. 
def List_fun {A X : Set.C₀} (n : Singleton → X) (c : Pair A X → X) 
: Set.hom ((list_algebra_functor A).map_obj X) X :=
  begin
    have test : Either Singleton (Pair A X) = (list_algebra_functor A).map_obj X := by refl,
    rw ←test,
    intro x,
    cases x,
    { exact n x },
    { exact c x }
  end

-- This is the Initial F-algebra for the 1 + 𝔸 × X functor.
-- X has type List 𝔸
-- The morphism 𝔽 (X) → X  consists of a function that return Nil and one that Constructs a Cons from A × X
def initial_list_algebra (A : Set.C₀) : (AlgebraCategory (list_algebra_functor A)).C₀ := {
  object := List A,
  function := List_fun (λ _, List.nil) (λ x, List.cons (fst x) (snd x))
}

-- In the category of the 1 + 𝔸 × X functor, fold is the constructor of catamorphisms.
-- Given a morphism 𝔽 (X) → X of an F-algebra B in the category,
-- fold constructs a morphism from the object of the initial algebra to the object of B.
def fold {A B : Set.C₀} : (Set.hom ((list_algebra_functor A).map_obj B) B) → Set.hom (List A) B :=
begin
  have test : (list_algebra_functor A).map_obj B = Either Singleton (Pair A B) := by refl,
  rw test,
  intros f x,
  induction x,
  case List.nil {
    exact f (Either.left Singleton.star)
  },
  case List.cons : hd _ ih {
    exact f (Either.right ⟨hd, ih⟩)
  }
end

-- Proof that fold applied to a morphism 𝔽 (X) → X of an F-algebra B is indeed a homomorphism 
def init_hom  {S : Set.C₀} (B : Falgebra (list_algebra_functor S)) : Fhomomorphism (initial_list_algebra S) B := 
{
  morph := fold B.function,
  square_proof := 
  begin
    apply funext,
    intro l,
    -- Since composition in the Set category (g ∘ f) is equivalent to applying g to f
    -- Therefore, we can rewrite the 2 sides of the equation.
    have h : Set.compose (fold B.function) (initial_list_algebra S).function l 
    = fold B.function ((initial_list_algebra S).function l) := by refl,
    rw h,

    have h1 : Set.compose B.function ((list_algebra_functor S).map_hom (fold B.function)) l =
    B.function (((list_algebra_functor S).map_hom (fold B.function)) l) 
     := by refl,
    rw h1,
    
    -- Since the result of 𝔽(X) is a coproduct, we have 2 cases that we need to cover.
    cases l,
    case Either.left : s {
      -- We apply the 𝔽(X) → X morphism of the initial algebra.
      have h2 : fold B.function ((initial_list_algebra S).function (Either.left s))
      = fold B.function (List.nil) := by refl,
      rw [h2],
      -- We apply fold to Nil
      have h3 : fold B.function (List.nil) = B.function (Either.left Singleton.star)
      := by refl,
      rw [h3],
      -- We apply the morphism mapping of 𝔽
      have h4 : B.function (((list_algebra_functor S).map_hom (fold B.function)) (Either.left s))
      = B.function (Either.left s) := by refl,
      rw [h4],
      -- We now prove that The singleton element is always ⋆
      have h5 : s = Singleton.star :=
        begin 
          cases s,
          refl,
        end,
      rw [h5],
    },
    case Either.right : p {
      -- We apply the 𝔽(X) → X morphism of the initial algebra.
      have h2 : fold B.function ((initial_list_algebra S).function (Either.right p))
      = fold B.function (List.cons (fst p) (snd p)) := by refl,
      rw [h2],
      -- We apply fold to Cons 𝔸 X
      have h3 : fold B.function (List.cons (fst p) (snd p))
       = B.function (Either.right ⟨(fst p), (fold B.function (snd p))⟩)
      := by refl,
      rw [h3],
      -- We apply the morphism mapping of 𝔽 to rewrite the right-hand side of the equation.
      have h4 : B.function (((list_algebra_functor S).map_hom (fold B.function)) (Either.right p))
      = B.function (Either.right ⟨(fst p), (fold B.function (snd p))⟩) := by refl,
      rw [h4],
    },
  end,
} 

-- Proof that the initial list F-algebra is indeed the initial object in the Algebra category of the 1 + 𝔸 × X functor
def initial_list_algebra_proof (A : Set.C₀) : initial ((AlgebraCategory (list_algebra_functor A))) := 
{
  -- The initial object is the List A F-algebra
  object := initial_list_algebra A,
  -- The unique morphism to any other F-algebra is the fold homomorphism
  exist_morph := init_hom, 
  -- Proof that the homomorphism is unique
  is_unique := 
    begin
      intros X f,
      simp [init_hom],
      cases f,
      -- In order to prove that 2 homomorphisms are equal it is enough to prove
      -- that the underlying morphisms are equal, their respecive square diagrams will also be the same.
      have test : f_morph = fold X.function :=
        begin
          apply funext,
          intro x,
          -- Working with Lists requires the use of a proof by induction.
          induction x,
          case List.nil {
            -- We apply fold to Nil
            have temp1 : fold X.function List.nil = X.function (Either.left Singleton.star) := by refl,
            simp [temp1],
            -- Now we move to the left-hand side of the equation and show that Nil is equal to
            -- applying the 𝔽(X) → X morphism of the initial algebra to 1. (Since by definition of "initial_list_algebra" it maps 1 to Nil).
            have temp2 : f_morph List.nil = f_morph ((initial_list_algebra A).function (Either.left Singleton.star)) := by refl,
            simp [temp2],
            -- Transform function application into Set composition.
            have temp3 : f_morph ((initial_list_algebra A).function (Either.left Singleton.star)) = (Set.compose f_morph (initial_list_algebra A).function) (Either.left Singleton.star) := by refl,
            simp [temp3],
            -- Apply the fact that the morphism makes its square diagram commute to the left-hand side.
            -- We go from:                       to:
            --              φ
            --       𝔽(⋆)   →  Nil               𝔽(⋆)
            --                                    
            --                  ↓ f         𝔽(f)  ↓
            --  
            --                  Y                𝔽(⋆)   →  Y
            --                                          ψ
            have temp4 : (Set.compose f_morph (initial_list_algebra A).function) (Either.left Singleton.star) = (Set.compose X.function ((list_algebra_functor A).map_hom f_morph)) (Either.left Singleton.star) := by simp [f_square_proof],
            simp [temp4],
            -- Transform Set composition into function applicaion.
            have temp5 : Set.compose X.function ((list_algebra_functor A).map_hom f_morph) (Either.left ⋆) = X.function (((list_algebra_functor A).map_hom f_morph) (Either.left ⋆)) := by refl,
            simp [temp5],
            -- Apply 𝔽's morphism mapping.
            have temp6 : (list_algebra_functor A).map_hom f_morph (Either.left Singleton.star) = Either.left Singleton.star := by refl,
            simp [temp6],
          },
          case List.cons : hd tl ih {
            -- Apply fold on the right-hand side. 
            have temp1 : fold X.function (List.cons hd tl) = X.function (Either.right ⟨hd, fold X.function tl⟩) := by refl,
            simp [temp1],
            -- Now we can apply our inductive hypothesis on the right-hand side.
            simp [←ih],
            -- We can now move to the left-hand side of the equation.
            -- We can show that Cons hd tl is equal to applying the 𝔽(X) → X morphism of the initial algebra to a Pair of hd and tl (by the definition of the morphism).
            have temp2 : f_morph (List.cons hd tl) = Set.compose f_morph (initial_list_algebra A).function (Either.right ⟨hd, tl⟩) := by refl,
            simp [temp2],
            -- Since the morphism makes its square diagram commute, we can apply this property and transform the left-hand side, similarly to the base case.
            -- We go from:                             to:
            --                    φ
            --       𝔽(⟨hd,tl⟩)   →  Cons hd tl        𝔽(⟨hd,tl⟩)
            --                                    
            --                            ↓ f          𝔽(f) ↓
            --  
            --                            Y            𝔽(⟨hd,f (tl)⟩)   →  Y
            --                                                          ψ
            have temp3 : Set.compose f_morph (initial_list_algebra A).function (Either.right ⟨hd, tl⟩) = Set.compose X.function ((list_algebra_functor A).map_hom f_morph) (Either.right ⟨hd, tl⟩) := by simp [f_square_proof],
            simp [temp3],
            -- Not we need to simplify our state. We transform Set composition to function application.
            have temp4 : Set.compose X.function ((list_algebra_functor A).map_hom f_morph) (Either.right ⟨hd, tl⟩) = X.function (((list_algebra_functor A).map_hom f_morph) (Either.right ⟨hd, tl⟩)) := by refl,
            simp [temp4],
            -- We can now apply 𝔽's morphism mapping to end up with ⟨hd,f (tl)⟩
            have temp5 : (list_algebra_functor A).map_hom f_morph (Either.right ⟨hd, tl⟩) = Either.right ⟨hd, f_morph tl⟩ := by refl,
            simp [temp5],
          }
        end,
      simp [test]
    end
}