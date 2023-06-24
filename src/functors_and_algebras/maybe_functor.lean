import instances.Set_category
import functors
import .tools

namespace category_theory

-- F functor : X → 1 + X
-- This functor is used for the Maybe algebra.
-- We can represent natural numbers with it.
-- We can imagine that the Singleton element is 0 and X is succ (ℕ)
-- which represents a successor of the previous element (i.e. succ (0) is 1). 
def maybe_algebra_Functor : Set ⇒ Set :=
{
  -- Objects are mapped to 1 + X
  map_obj := λ X, Either Singleton X,
  -- Morphisms are mapped based on 2 cases:
  -- 1) The Singleton element is unchanged,
  -- 2) X is mapped to f (X)
  map_hom := 
  begin 
    intros x y f E,
    cases E,
    case Either.left : a {
      exact Either.left a
    },
    case Either.right : b {
      exact Either.right (f b)
    }
  end,
  -- To prove that Identity is preserved we again have 2 cases:
  -- 1) Singleton is unchanged, since no function is applied to it.
  -- 2) The second case is proving that 1 + Id (X) = Id (1 + X), when (1 + X) is evaluated to X => Id (X) = Id (X).
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
      refl
    }
  end,
  -- The preservation of composition is proven similary to that of Identity. 
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
      refl,
    }
  end
}

end category_theory