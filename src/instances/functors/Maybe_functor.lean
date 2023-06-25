import instances.Set_category
import functors.functor
import functors_and_algebras.tools

open category_theory

inductive Maybe (α : Type*)
  | none : Maybe
  | some : α → Maybe

def Maybe.fmap {α β : Type*} (f : α → β) : Maybe α → Maybe β
  | Maybe.none := Maybe.none
  | (Maybe.some x) := Maybe.some (f x)

-- Example of the Maybe functor 
-- as known from Functional Programming Languages
def Maybe.functor : Set ⇒ Set :=
{
  -- Objects are mapped to the Maybe type.
  map_obj := λ A, Maybe A,
  -- Morphisms are mapped by chosing between two cases.
  -- 1) Given input None, None is returned.
  -- 2) Given input Some a, Some (f a) is returned.
  map_hom := λ _ _ f, Maybe.fmap f,
  /- begin -/
  /-   intros α β f as, -/
  /-   induction as, -/
  /-   case Maybe.none { -/
  /-     exact Maybe.none -/
  /-   }, -/
  /-   case Maybe.some : x { -/
  /-     exact Maybe.some (f x) -/
  /-   } -/
  /- end, -/
  --Preservation of composition is proved by using the 2 cases of the morphism mapping.
  -- and the fact that we can compose f and g. Lean understands this and helps us with writing short proofs.
  comp :=
  begin
    intros _ _ _ f g,
    apply funext,
    intro xs,
    induction xs,
    case Maybe.none {
      refl
    },
    case Maybe.some : x {
      refl
    }
  end,
  -- Preservation of identity is also proved by utilizing the 2 cases of the morhpism mapping
  -- and the fact that the identity morphism maps an element to itself.
  -- Lean understands this and helps us with writing short proofs.
  id :=
  begin
    intros _,
    apply funext,
    intro xs,
    induction xs,
    case Maybe.none {
      refl
    },
    case Maybe.some : x {
      refl
    }
  end
}
