import functors.functor
import instances.Product_category

namespace category_theory

-- Δ : C → C × C, Δ(x) = (x, x), ∀ x ∈ 𝒞₀ ∪ Hom𝒞.
def diagonal_functor (𝒞 : category) : 𝒞 ⇒ (Product 𝒞 𝒞) :=
{
  map_obj := λ (c : 𝒞), (c, c),
  map_hom := λ {c d : 𝒞} (h : 𝒞.hom c d), (h, h),
  id :=
    begin
      intros,
      refl,
    end,
  comp :=
    begin
      intros,
      refl,
    end,
}
-- notation
infixr `Δ`:90 := diagonal_functor

end category_theory