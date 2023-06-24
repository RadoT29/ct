import functors.functor
import universal_properties_alt.binary_product
import universal_properties_alt.product_morphism
import instances.Product_category

namespace category_theory

-- This file defines the product functor from the product category C×C to C.
-- In order for it to exist, C must be a category with binary products (ie., 
-- the product of any two objects c and d in C, c×d, must exist).
--
-- It maps each object ⟨c, d⟩ in C×C to the product object in C c×d.
-- It also maps each morphism ⟨f, g⟩ in C×C with f : hom_C(c, d) and
-- g : hom_C(i, j), to the morphism f×g : hom_C(c×i, d×j) that makes the
-- diagram commute:
--       c ←   c×i   → i
--              |
--     f ↓  f×g |    ↓ g
--              ↓
--       d ←   d×j   → j

-- Definition for the product functor.
def product_functor (𝒞 : category) [has_all_products 𝒞] : (Product 𝒞 𝒞) ⇒ 𝒞 :=
{
  -- maps each object ⟨c, d⟩ to c×d.
  map_obj := λ (c : Product 𝒞 𝒞), (po c.fst c.snd).p,
  -- maps each morphism ⟨f,g⟩ to the product f×g.
  map_hom := λ {p q : Product 𝒞 𝒞} (m : (Product 𝒞 𝒞).hom p q),
    begin
      -- for ease of use we define consistent with previous notation:
      let f := m.fst, -- f as the left element of the tuple morphism m
      let g := m.snd, -- g as the right element of m
      -- now we just apply product_morphism
      let fxg := product_morphism f g,
      exact fxg
    end,
  -- Now we need to prove that the functors preserves identity morphisms,
  -- so the identity morph of ⟨c,d⟩ in C×C is mapped to the identity morph
  -- of c×d in C.
  id :=
    begin
      intros,
      simp,
      rw identity_morphism_of_product,
      refl,
    end,
  comp :=
    begin
      intros,
      simp,
      symmetry,
      apply product_of_composible_morphisms,
    end,
}

end category_theory