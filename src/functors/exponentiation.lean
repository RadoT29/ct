import functors.functor
import universal_properties_alt.binary_product
import universal_properties_alt.exponent

namespace category_theory

-- This file contains the definition for the exponentiation
-- functor.
-- Check out Pierce, example 71 (2.11, pg. 32).
--
-- For a category C with binary products and exponentiation
-- and a given object c in C, we define the functor (─)^c
-- mapping objects b to the exponentiation b^c and morphisms
-- f:b→d to the left component of the unique morphism between
-- b^c×c and d^c×c given by f ∘ ev_b^c : b^c×c → d (defined as
-- exp_hom in exponent.lean).
def exponentiation_functor {C : category} [has_all_products C] [has_exponentiation C] (c : C) : functor C C :=
{
  -- b → b^c
  map_obj := λ (b : C), (exp b c).ob,
  -- f:b→d → unique morphism as introduced in the description
  map_hom := λ {b d : C} (f : C.hom b d), exp_hom c f,
  -- id x^c = unique morphism from x^c to x^c given by (id x) ∘ ev_x^c
  -- we prove this by invoking the uniqueness property in this diagram
--                  ev_X^c
--         X^c × c    →     X  
--             ↑         ↗
-- Id_X^c×Id_c |       ↗  ev_X^c
--             |     ↗
--         X^c × c
  id :=
    begin
      intro,
      unfold exp_hom,
      rw C.right_id,
      symmetry,
      apply (exp X c).uu (exp X c).ob (exp X c).ev (C.id (exp X c).ob),
      rw ← identity_morphism_of_product,
      rw C.left_id,
    end,
  -- show the unique arrow generated by exp_hom via g∘f is equal to the
  -- composition of the arrows generated by exp_hom for g and f, respectively.
  -- exp_hom g∘f is the unique morphism from X^c to Z^c given by g∘f∘ev_X^c
  -- so if we can show g∘f∘ev_X^c = (exp_hom g)∘(exp_hom f) then we're done.
  comp :=
    begin
      intros,
      -- unfold exp_hom's definition to make it clear it's an unique arrow
      rw exp_hom,
      -- move parantheses around, f∘ev_X^c generates an exp_hom to Y^c
      rw ← C.assoc,
      rw ← simp_exp_hom,
      -- then if we move parantheses again, g∘ev_Y^c generates another exp_hom to Z^c
      rw C.assoc,
      rw ← simp_exp_hom,
      -- now we can combine the products of morphisms
      -- (change first from product_morphism to pm since that's what we defined
      -- the  omposition lemma with)
      rw refl_product_morphism_pm,
      rw refl_product_morphism_pm,
      rw ← C.assoc,
      rw product_of_composible_morphisms,
      rw ← refl_product_morphism_pm,
      -- simplify the identity composition, now we get a statement that's clearly
      -- true by exponentiation's uniqueness property.
      rw C.left_id,
      symmetry,
      apply (exp Z c).uu (exp X c).ob (C.compose (exp Z c).ev (product_morphism (C.compose (exp_hom c g) (exp_hom c f)) (C.id c))) (C.compose (exp_hom c g) (exp_hom c f)),
      refl,
    end,
}

end category_theory