import ..category

open category_theory

universe u
def Types : category :=
{
  C₀ := Type u,
  hom := λ X Y, X → Y,
  id  := λ X, λ (x : X), x,
  compose := λ {X Y Z} (g : Y → Z) (f : X → Y), g ∘ f,
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
