import functors.functor
namespace category_theory

-- Creates the identity functor of a category.
-- This maps each object and morphism to itself.
def Id (𝒞 : category) : 𝒞 ⇒ 𝒞 :=
{
  map_obj := λ X : 𝒞, X,
  map_hom := λ X Y : 𝒞, λ f, f,
  id :=
    begin
      intro X,
      refl,
    end,
  comp :=
    begin
      intros,
      refl,
    end,
}

end category_theory
