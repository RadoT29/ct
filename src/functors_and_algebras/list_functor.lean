import instances.Set_category
import functors
import .tools
namespace category_theory

-- F𝔸 functor : X → 1 + (𝔸 × X)
-- This functor can be used for a List Algebra.
-- We can imagine that Nil is 1 (i.e a singleton element) and 𝔸 × X is Cons 𝔸 X,
-- where 𝔸 is the head of the list with Type 𝔸 and X is the tail.
def list_algebra_functor (A : Set.C₀) : Set ⇒ Set :=
{
  -- Objects are mapped to 1 + (𝔸 × X)
  map_obj := λ X, Either Singleton (Pair A X),
  -- Morphisms are mapped based on 2 cases:
  -- 1) The Singleton element is unchanged,
  -- 2) (𝔸 × X) is mapped to ( 𝔸 × f (X) )
  map_hom := 
  begin 
    intros x y f E,
    cases E,
    case Either.left : a {
      exact Either.left a
    },
    case Either.right : b {
      exact Either.right ⟨fst b, f (snd b)⟩
    }
  end,
  -- To prove that Identity is preserved we again have 2 cases:
  -- 1) Singleton is unchanged, since no function is applied to it.
  -- 2) (𝔸 × Id (X)) = Id (𝔸 × X) is proven by showing that (𝔸 × Id (X)) = (𝔸 × X) = Id (𝔸 × X)
  id :=
  begin
    intro _,
    simp,
    apply funext,
    intro x,
    cases x,
    case Either.left : a {
      simp,
      refl,
    },
    case Either.right : b {
      simp,
      -- (𝔸 × Id (X)) = (𝔸 × X)
      have h : ⟨fst b,Set.id X (snd b)⟩ 
        = ⟨fst b, snd b⟩ := by refl,
      rw h,
      -- We introduce the pair equality lemma, stating that
      -- a pair A is equal to a pair constructed by taking the first and second element of A.
      -- Lean is not able to prove it by itself and needs an explicit proof.
      simp [pair_eq b],
      -- Lean can prove (𝔸 × X) = Id (𝔸 × X) by itself.
      refl,
    }
  end,
  -- To prove that Identity is preserved we again have 2 cases:
  -- 1) Singleton is unchanged, since no function is applied to it.
  -- 2) (𝔸 × g ∘ f (X)) = g ∘ f (𝔸 × X) is proven by showing that (𝔸 × g ∘ f (X)) = (𝔸 × X) = g ∘ f (𝔸 × X)
  -- the steps in the proof are similar to the proof above.
  comp:= 
  begin
    intros _ _ _ f g,
    simp,
    apply funext,
    intro x,
    cases x,
    case Either.left : a {
      simp,
      refl,
    },
    case Either.right : b {
      simp,
      have h : ⟨fst b, Set.compose g f (snd b)⟩ 
        = ⟨fst b, g (f (snd b))⟩ := by refl,
      rw h,
      refl,
    }
  end
}

end category_theory