import category
import functors

namespace category_theory

-- Definition 2.1 https://ncatlab.org/nlab/show/adjoint+functor
-- in terms of natural bijections of hom-sets. (Mac Lane pg. 80)

-- L and R are the left adjoint and right adjoint functors, respectively.
-- Note that functor_map morphs a morphism via a functor,
-- while the object morph via a functor is done with a function application
-- as functor is coerced to a function that morphs the objects
-- (eg. L c for functor L : C → D and object c : C).

-- The naturality conditions are defined for all pairs ⟨c, d⟩ of objects and
-- arbitrary morphism dₕ in 𝒟(L c, d).
structure adjunction_hom {𝒞 𝒟 : category} (L : 𝒞 ⇒ 𝒟) (R : 𝒟 ⇒ 𝒞) :=
(φ : Π {c : 𝒞} {d : 𝒟}, (𝒟.hom (L c) d) → (𝒞.hom c (R d)))

-- Homset mapping should be isomorphic.
(φr : Π {c : 𝒞} {d : 𝒟}, (𝒞.hom c (R d)) → (𝒟.hom (L c) d))
(sect : ∀ {c : 𝒞} {d : 𝒟} (h : 𝒞.hom c (R d)), (φ ∘ φr) h = h)
(retr : ∀ {c : 𝒞} {d : 𝒟} (k : 𝒟.hom (L c) d), (φr ∘ φ) k = k)

-- Naturality in c means this diagram commutes for all morphisms h : 𝒞(c', c):
--              φ
--   𝒟(L c,  d) → 𝒞(c,  R d)
--
--   (∘L h) ↓           ↓ (∘h)
--
--   𝒟(L c', d) → 𝒞(c', R d)
--              φ
(naturality_c : ∀ (c : 𝒞) (d : 𝒟) (dₕ : 𝒟.hom (L c) d),
              ∀ {c' : 𝒞} (h : 𝒞.hom c' c), 𝒞.compose (φ dₕ) h = φ (𝒟.compose dₕ (L.map_hom h)))

-- While naturality in d means this diagram commutes for all morphisms k : 𝒟(d, d'):
--              φ
--   𝒟(L c,  d) → 𝒞(c,  R d)
--
--     k ↓           ↓ R k
--
--   𝒟(L c, d') → 𝒞(c, R d')
--              φ
(naturality_d : ∀ (c : 𝒞) (d : 𝒟) (dₕ : 𝒟.hom (L c) d),
              ∀ {d' : 𝒟} (k : 𝒟.hom d d'), 𝒞.compose (R.map_hom k) (φ dₕ) = φ (𝒟.compose k dₕ))

-- Since the mapping is isomorphic, we also have duals for the naturality properties, where
-- the arrow corresponding to φ is reversed.
--
-- ∀ h : 𝒞(c', c):
--              φr
--   𝒞(c,  R d) → 𝒟(L c,  d)
--
--   (∘h) ↓            ↓ (∘L h)
--
--   𝒞(c', R d) → 𝒟(L c', d)
--              φr
(naturality_cr : ∀ (c : 𝒞) (d : 𝒟) (cₕ : 𝒞.hom c (R d)),
              ∀ {c' : 𝒞} (h : 𝒞.hom c' c), 𝒟.compose (φr cₕ) (L.map_hom h) = φr (𝒞.compose cₕ h))

--
-- ∀ k : 𝒟(d, d'):
--              φr
--   𝒞(c,  R d) → 𝒟(L c,  d)
--
--   R k ↓            ↓ k
--
--   𝒞(c, R d') → 𝒟(L c, d')
--              φr
(naturality_dr : ∀ (c : 𝒞) (d : 𝒟) (cₕ : 𝒞.hom c (R d)),
              ∀ {d' : 𝒟} (k : 𝒟.hom d d'), 𝒟.compose k (φr cₕ) = φr (𝒞.compose (R.map_hom k) cₕ))

end category_theory