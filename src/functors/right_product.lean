import functors.functor
import universal_properties_alt.binary_product
import universal_properties_alt.product_morphism

namespace category_theory

-- This file contains the definition for a useful but basic
-- functor, the right product functor.
-- Check out Pierce, example 64 (2.10, pg. 29).
--
-- For a category C with binary products and a given object
-- c in C, we can define the functor ─×c mapping objects b
-- to the product object b×c and morphisms  f:b→d to the
-- product of morphisms f×id_c (from b×c to d×c).
def r_product_functor {𝒞 : category} [has_all_products 𝒞] (c : 𝒞) : 𝒞 ⇒ 𝒞 :=
{
  -- b → b×c
  map_obj := λ (b : 𝒞), (po b c).p,
  -- f → f×id
  map_hom := λ {b d : 𝒞} (f : 𝒞.hom b d), product_morphism f (𝒞.id c),
  -- already proved (id c)×(id d) = id (c×d)
  id :=
    begin
      intro,
      rw identity_morphism_of_product,
    end,
  -- already proved (g∘f)×(g'∘f') = g×g' ∘ f×f'
  comp :=
    begin
      intros,
      rw refl_product_morphism_compose,
      rw 𝒞.left_id,
    end,
}

end category_theory