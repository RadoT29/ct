import functors.functor
import universal_properties_alt.binary_product
import universal_properties_alt.product_morphism

namespace category_theory

-- Defines the exponent object and its properties for two (specific) objects in C.
structure exponent {𝒞 : category} [has_all_products 𝒞] (b a : 𝒞) :=
-- has object b^a and arrow eval : (b^a × a) → b with universal property 
(ob : 𝒞)
(ev : 𝒞.hom (po ob a).p b)
-- for all other objects c with morphisms g from c×a to b, there is a unique morphism
-- g⋆ mapping c to b^a×a that makes the triangle in the diagram commute:
--           ev_b^a
--     b^a×a    →      b
--        ↑  
--  g⋆×idₐ|         ↗
--        |       ↗ g
--       c×a
-- Existence
(ue : Π (c : 𝒞) (g : 𝒞.hom (po c a).p b), 𝒞.hom c ob)
(ump : ∀ (c : 𝒞) (g : 𝒞.hom (po c a).p b), g = 𝒞.compose ev (product_morphism (ue c g) (𝒞.id a)))
-- Uniqueness
(uu : ∀ (c : 𝒞) (g : 𝒞.hom (po c a).p b) (h : 𝒞.hom c ob), g = 𝒞.compose ev (product_morphism h (𝒞.id a)) → h = ue c g)

-- Category with exponentiation.
class has_exponentiation (𝒞 : category) [has_all_products 𝒞] :=
(exp : Π (a b : 𝒞), exponent a b)

-- Short-hand for b^a.
def exp {𝒞 : category} [has_all_products 𝒞] [has_exponentiation 𝒞] (b a : 𝒞) := has_exponentiation.exp b a

-- Pierce example 71 (2.11, pg. 32)
-- Converts morphisms f:b → c to the unique morphism f*:b^a→c^a given by f∘ev_b^a : b^a×a → c.
--               ev_c^a
--      c^a × a    →     c  
--          ↑         ↗
-- unique   |       ↗  f ∘ ev_b^a
--          |     ↗
--      b^a × a
def exp_hom {𝒞 : category} [has_all_products 𝒞] [has_exponentiation 𝒞] (a : 𝒞) {b c : 𝒞} (f : 𝒞.hom b c)
: 𝒞.hom (exp b a).ob (exp c a).ob := (exp c a).ue (exp b a).ob (𝒞.compose f (exp b a).ev) 

-- Some useful lemmas.

-- eval with exp_hom acts as some sort of natural transformation (this diagram commutes:)
--                    ev_b^a
--            b^a × a   →      b
--
-- exp_hom × Id_a ↓            ↓ f
-- a f 
--            c^a × a   →      c
--                    ev_c^a
--
-- So it does not matter whether we eval the exponential and then apply f, or apply exp_hom f
-- and the eval the exponential.
lemma simp_exp_hom {𝒞 : category} [has_all_products 𝒞] [has_exponentiation 𝒞] (a : 𝒞) {b c : 𝒞}
(f : 𝒞.hom b c) : 𝒞.compose (exp c a).ev (product_morphism (exp_hom a f) (𝒞.id a)) = 𝒞.compose f (exp b a).ev :=
  begin
    unfold exp_hom,
    symmetry,
    -- this is exactly the mapping property
    exact (exp c a).ump (exp b a).ob (𝒞.compose f (exp b a).ev),
  end

end category_theory