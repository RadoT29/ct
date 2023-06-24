import category

open category_theory

-- Set
-- category of sets
def Set : category :=
{
  -- Type 0 in Lean is essentialy a set.
  C₀ := Type*,

  -- A morphism between two sets maps the elements from one set
  -- to the other, same as what a function between types does.
  hom := λ X Y, X → Y,

  -- The identity morphism maps each element to itself.
  id  := λ X, λ (x : X), x,

  -- Each morphism is a function, so morphism composition is the
  -- same as composition of the underlying functions.
  compose := λ {X Y Z} (g : Y → Z) (f : X → Y), g ∘ f,

  -- We can use the proofs from function.comp.
  left_id :=
    begin
      intros,
      apply function.comp.right_id,
    end,
  right_id :=
    begin
      intros,
      apply function.comp.left_id,
    end,
  assoc :=
    begin
      intros,
      apply function.comp.assoc,
    end,
}
