import instances.Set_category
import functors_and_algebras.tools
import .initial_list_algebra
import functors_and_algebras.list_functor
import functors_and_algebras.fusion_property
import instances.functors.List_functor

open category_theory
-- This file presents a proof that applying `filter`, followed by `length` on lists
-- is the same as applying the filter function during the process of counting, using the fusion property.

-- Before we begin with the proof, let's define the necessary utilities.

-- Simple recursive filter function
def filter {A : Set.C₀} : (A → bool)→ (List A) → (List A)
  | f List.nil := List.nil
  | f (List.cons hd tl) := if (f hd) then List.cons hd (filter f tl) else filter f tl

-- Filter represented as fold
def filter_as_fold {A : Set.C₀} (f : A → bool) : Set.hom (List A) (List A) :=
  fold (List_fun (λ _, List.nil) (λ p, if (f (fst p)) then List.cons (fst p) (snd p) else (snd p)))

-- Simple length function
def length {A : Set.C₀} : (List A) → nat 
  | List.nil := nat.zero
  | (List.cons hd tl) := nat.succ (length tl)

-- Length represented as fold
def length_as_fold {A : Set.C₀} : Set.hom (List A) nat :=
  fold (List_fun (λ _, nat.zero) (λ p, nat.succ (snd p)))

--The 2 lemmas below can be proven by using the uniqueness of the fold catamorphism
-- by presenting the length and filter functions as homomorphisms between 2 algebras.

-- Proof that the normal length function is the same as the one using fold
lemma fold_eq_length : ∀ {A : Set.C₀} (l : List A), length l = length_as_fold l :=
begin
  intros A l,
  induction l,
  case List.nil {
    refl,
  },
  case List.cons : hd tl ih {
    have h1 : length (List.cons hd tl) = nat.succ (length tl) := by refl,
    have h2 : length_as_fold (List.cons hd tl) = nat.succ (length_as_fold tl) := by refl,
    rw [h1,h2,ih],
  },
end

-- Proof that the normal filter function is the same as the one using fold
lemma fold_eq_filter : 
  ∀ {A : Set.C₀} (f : A → bool) (l : List A), filter f l = filter_as_fold f l := 
begin
  intros A f l,
  induction l,
  case List.nil {
    refl,
  },
  case List.cons : hd tl ih {
    have h1 : filter f (List.cons hd tl) = 
      if (f hd) then List.cons hd (filter f tl) else filter f tl := by refl,
    have h2 : filter_as_fold f (List.cons hd tl) = 
      if (f hd) then List.cons hd (filter_as_fold f tl) else filter_as_fold f tl := by refl,
    rw [h1,h2,ih],
  },
end

-- The algebra, where 𝔽(X) → X is length 
def alg_length {A : Set.C₀} (f : A → bool) : Falgebra (list_algebra_functor A) := {
  object := ℕ,
  function := List_fun (λ _, nat.zero) (λ p, nat.succ (snd p)),
}

-- The algebra, where 𝔽(X) → X is filter 
def alg_filter {A : Set.C₀} (f : A → bool) : Falgebra (list_algebra_functor A) := {
  object := List A,
  function := (List_fun (λ _, List.nil) (λ p, if (f (fst p)) then List.cons (fst p) (snd p) else (snd p))),
}

-- The algebra, where 𝔽(X) → X is ( length ∘ filter )
def alg_length_filtered {A : Set.C₀} (f : A → bool) : Falgebra (list_algebra_functor A) := {
  object := ℕ,
  function := List_fun (λ _, nat.zero) (λ p, if (f (fst p)) then nat.succ (snd p) else (snd p)),
}

-- The homomorphism from the filter algebra to the composed filter and length algebra 
def hom_f_l {A : Set.C₀} (f : A→ bool) : Fhomomorphism (alg_filter f) (alg_length_filtered f) := {
  -- The morphism is simply length
  morph := length_as_fold,
  -- To prove that the length morphism is indeed a homomorphism, it is required to prove that it commutes its square diagram.
  square_proof := 
  begin
    apply funext,
    intro x,
    cases x,
    -- Given the empty list, the result is the same for both paths. 
    case Either.left {
      refl,
    },
    -- The more interesting case is when we encounter a non-empty list.
    case Either.right : p {
      -- Rewrite composition in the category of sets as function application g (f x) on the right-hand side.
      have h1 : Set.compose (alg_length_filtered f).function ((list_algebra_functor A).map_hom length_as_fold) (Either.right p) =
      (alg_length_filtered f).function (((list_algebra_functor A).map_hom length_as_fold) (Either.right p)) := by refl,
      rw h1,
      -- Apply the morphism mapping of the 1 + (𝔸 × X) functor, which applies the length morphism to X.
      have h2 : ((list_algebra_functor A).map_hom length_as_fold) (Either.right p) = 
        Either.right ⟨fst p, length_as_fold (snd p)⟩ := by refl,
      rw h2,

      -- Rewrite composition in the category of sets as function application g (f x) on the right-hand side.
      have h3 : Set.compose length_as_fold (alg_filter f).function (Either.right p) = 
      length_as_fold ((alg_filter f).function (Either.right p)) := by refl,
      rw h3,
      -- The 2 paths use if contiditons
      -- Rewrite the definition of the filter algebra 𝔽(X) → X morphism
      have h4 : (alg_filter f).function (Either.right p) = (λ x, if (f (fst x)) then List.cons (fst x) (snd x) else snd x) p := by refl,
      rw h4,
      -- Rewrite the definition of the composed algebra 𝔽(X) → X morphism
      have h5 : (alg_length_filtered f).function (Either.right ⟨fst p,length_as_fold (snd p)⟩) = 
      if (f (fst ⟨fst p,length_as_fold (snd p)⟩)) 
      then nat.succ (snd ⟨fst p,length_as_fold (snd p)⟩) else snd ⟨fst p,length_as_fold (snd p)⟩:= by refl,
      rw h5,
      -- Simplify the lambda expression
      have h7 : ((λ (x : Pair A (List A)), ite ↥(f (fst x)) (List.cons (fst x) (snd x)) (snd x)) p) =
        ite ↥(f (fst p)) (List.cons (fst p) (snd p)) (snd p) := by refl,
      rw h7,

      -- We have now rewritten both sides of the equation so that they have the if (f (fst p)) statement.
      -- An if condition has 2 cases (true and false), therefore we can now explore each case and substitute 
      -- either true or false in the plase of (f (fst p)).
      cases (f (fst p)),
      case bool.ff {
        -- When the condition is false, that means that the head of the list will be filtered out. Therefore,
        -- we only consider the length of the tail.
        -- This is reflected in both paths of the diagram.
        -- The down-right path will simply return the element Y in the resultin product by definition of ψ for the algebra.
        --
        --                 𝔽(𝔸 × X)
        --                                    
        -- 𝔽(length_as_fold)  ↓
        --  
        --                 𝔽(𝔸 × Y)       →       Y
        --                       ψ - if false then Y
        have h6 : ite ↥ff (snd ⟨fst p,length_as_fold (snd p)⟩).succ (snd ⟨fst p,length_as_fold (snd p)⟩) =
        length_as_fold (snd p) := by refl,
        rw h6,
        -- The right-down path will first result in a list, which does not contain the head element 𝔸.
        -- Then only that list will be considered for `length`
        --                φ - if false then X
        --       𝔽(𝔸 × X)   → X (The second element in (𝔸 × X))
        --                                    
        --                   ↓ length_as_fold
        --  
        --                  Y  
        have h7 : (ite ↥ff (List.cons (fst p) (snd p)) (snd p)) = snd p := by refl,
        rw h7,
      },
      -- When the condition is true, the scheme drawn above, changes by :
      -- 1)   𝔽(𝔸 × Y)       →     (Y + 1), now ψ does not only return Y, but adds 1 to it.
      -- 2)   𝔽(𝔸 × X)   → List 𝔸 X, now φ does not filter out the head of the list. Therefore the final result has length + 1.
      case bool.tt {
        have h6 : (ite ↥tt (List.cons (fst p) (snd p)) (snd p)) = List.cons (fst p) (snd p) := by refl,
        rw h6,
        have h7 : ite ↥tt (snd ⟨fst p,length_as_fold (snd p)⟩).succ (snd ⟨fst p,length_as_fold (snd p)⟩) =
          nat.succ (length_as_fold (snd p)) := by refl,
        rw h7,
        have h8 : length_as_fold (List.cons (fst p) (snd p)) =  nat.succ (length_as_fold (snd p)) := by refl,
        rw h8,
      },
    },
  end,
}

-- Proof that composing length and filter is equal to folding by filtering while counting (i.e. the catamorphism from list to the composed algebra).
def eq_length_comp_filter_cat : ∀ {A : Set.C₀} (f : A → bool), Set.compose length (filter f) = fold (alg_length_filtered f).function :=
begin
  intros A f,
  -- Apply the fustion property for the homomorphism from the filter algebra to the composed algebra.
  -- In order to utilize it we need to transform the equation to one that uses the unique morphism from the initial algebra to the composed one,
  -- as well as a composition of the unique morphisms from the initial algebra to the filter algebra and the homomorphism defined above.
  -- In order to adhere to this, we need to prove that filter is the catamorphism from the initial list algebra to the filter algebra
  -- and rewrite length as the homomorphism from the filter algebra to the composed one.
  have h := fusion (initial_list_algebra_proof A) (alg_filter f) (alg_length_filtered f) (hom_f_l f).morph (hom_f_l f).square_proof,
  apply funext,
  intro l,
  -- Apply the fact that composition in the set category is equal to function application g∘f x = g (f x)
  have h1 : Set.compose length (filter f) l = length ((filter f) l) := by refl,
  rw h1,
  -- We now apply the lemmas that state that the normal filter and length functions can be defined as fold.
  rw [fold_eq_filter f l],
  rw [fold_eq_length (filter_as_fold f l)],
  -- Rewrite function application to Category composition.
  have h2 : length_as_fold ((filter_as_fold f) l) = Set.compose length_as_fold (filter_as_fold f) l := by refl,
  rw h2,
  -- Apply the fact that the morphism of the homomorphism between the filter algebra and the composed one is `indeed length_as_fold` 
  have h3 : (hom_f_l f).morph = length_as_fold := by refl,
  rw ←h3,
  -- Apply the fact that the catamorphism from the initial algebra to the filter algebra is indeed the `filter_as_fold` morphism
  have h4 : ((initial_list_algebra_proof A).exist_morph (alg_filter f)).morph = filter_as_fold f := by refl,
  rw ←h4,
  -- Apply the fact that fold with the composed function is indeed a catamorphism to the composed algebra.
  have h5 : fold (alg_length_filtered f).function = ((initial_list_algebra_proof A).exist_morph (alg_length_filtered f)).morph := by refl,
  rw h5,
  -- The equation is now rewriten to a state, which lean can pick up, so we can simply substitute the fusion property.
  simp [h],
end