import functors.functor
import universal_properties_alt.binary_product

namespace category_theory

-- Constructs the bundle of cxi with its morphisms to d and j via c and i
--       c ← cxi → i
--
--     f ↓         ↓ g
--
--       d         j
def product_morphism_bundle {𝒞 : category} {c d i j : 𝒞} (cxi : binary_product c i)
(f : 𝒞.hom c d) (g : 𝒞.hom i j) : binary_product_bundle d j :=
{
  x := cxi.p,
  x₁ := 𝒞.compose f cxi.p₁,
  x₂ := 𝒞.compose g cxi.p₂,
}

-- Via the universal property and with the bundle defined above, there is a mapping from cxi to dxj.
def product_morphism {𝒞 : category} {c d i j : 𝒞} {cxi : binary_product c i} {dxj : binary_product d j}
(f : 𝒞.hom c d) (g : 𝒞.hom i j)
: 𝒞.hom cxi.p dxj.p := dxj.ue (product_morphism_bundle cxi f g)

-- Short-hand for the f×g.
def pm {𝒞 : category} {c d i j : 𝒞} (cxi : binary_product c i) (dxj : binary_product d j)
(f : 𝒞.hom c d) (g : 𝒞.hom i j) : 𝒞.hom cxi.p dxj.p := @product_morphism 𝒞 c d i j cxi dxj f g

--       c ←   c×i   → i
--              |
--     f ↓  f×g |    ↓ g   commutes
--              ↓
--       d ←   d×j   → j
lemma product_morphism_commutes {𝒞 : category} {c d i j : 𝒞}
(cxi : binary_product c i) (dxj : binary_product d j) (f : 𝒞.hom c d) (g : 𝒞.hom i j)
: 𝒞.compose f cxi.p₁ = 𝒞.compose dxj.p₁ (product_morphism f g) 
∧ 𝒞.compose g cxi.p₂ = 𝒞.compose dxj.p₂ (product_morphism f g) :=
  begin
    -- Use the construction of the product morphism.
    unfold product_morphism,
    -- Split into the left and right squares of the diagram.
    split,
    -- Using the definition of the mapping property, we get proofs of the commuting diagrams.
    apply (dxj.ump (product_morphism_bundle cxi f g)).left,
    apply (dxj.ump (product_morphism_bundle cxi f g)).right,
  end

-- Proving id c×d = (id c) × (id d).
lemma identity_morphism_of_product {𝒞 : category} {c d : 𝒞} (cxd : binary_product c d)
: 𝒞.id cxd.p = product_morphism (𝒞.id c) (𝒞.id d) :=
  begin
    -- We have two morphisms from c×d to c×d : 𝒞.id c×d and (𝒞.id c)×(𝒞.id d).
    -- We're using the uniqueness property of product c×d to show that 𝒞.id c×d, a morph
    -- from c×d to c×d, is same as (𝒞.id c)×(𝒞.id d), a preexisting morph between the same objects.
    --
    -- b is a bundle containing c×d and its two maps to c and d (the identities).
    let b := product_morphism_bundle cxd (𝒞.id c) (𝒞.id d),
    apply cxd.uu b (𝒞.id cxd.p),
    -- So now what we need to prove is essentially that 𝒞.id (p₁ c×d) = p₁ (𝒞.id c×d)
    -- (projecting the identity of c×d to c is identical to the identity of projecting c×d to c),
    -- trivial. We just need to swap around the 𝒞.id's to make Lean figure out the two definitions
    -- are identical.
    split,
    rw 𝒞.left_id cxd.p₁,
    rw ← 𝒞.right_id cxd.p₁,
    refl,
    rw 𝒞.left_id cxd.p₂,
    rw ← 𝒞.right_id cxd.p₂,
    refl,
  end

-- Proving that the product of two composed morphisms is the composition of two product morphisms.
-- For f, f', g, g' morphisms for which g∘f and g'∘f' makes sense, and their domains, codomains
-- admit products in C.
-- So prove that the "direct" morph from c×c' to e×e', (g∘f)×(g'∘f'), is equal to the composite:
-- (g×g')∘(f×f').
--       c ←   c×c'   → c'                            c ←   c×c'   → c'
--              |                                            |
--     f ↓  ff' |       ↓ f'                          ↓      |      ↓
--              ↓                                            |
--       d ←   d×d'   → d'   and if we ignore d,  g∘f ↓    × |      ↓ g'∘f'
--              |                                            |
--     g ↓  gg' |       ↓ g'                          ↓      |      ↓
--              ↓                                            ↓
--       e ←   e×e'   → e'                            e ←   e×e'  → e'
lemma product_of_composible_morphisms {𝒞 : category} {c c' d d' e e' : 𝒞}
{cp : binary_product c c'} {dp : binary_product d d'} {ep : binary_product e e'}
(f : 𝒞.hom c d) (f' : 𝒞.hom c' d') (g : 𝒞.hom d e) (g' : 𝒞.hom d' e')
: 𝒞.compose (pm dp ep g g') (pm cp dp f f') = pm cp ep (𝒞.compose g f) (𝒞.compose g' f') :=
  begin
    -- Strategy: use the uniqueness property of e×e' to show that (g∘f)×(g'∘f') = (f×f')∘(g×g').
    -- To do that, we need to show that (f×f')∘(g×g') is also a product of morphisms from c×c' to e×e'.
    -- So, prove that 1. (f×f')∘(g×g') is a morph from c×c' to e×e' (obvious);
    --                2. g∘f maps c to e and g'∘f' maps c' to e' (obvious);
    --                3. (f×f')∘(g×g') makes the diagram for product of morphisms commute.
    -- For (3.), that means we have to show g ∘ f ∘ πc = πe (f×f')∘(g×g') and
    --                                      g'∘ f'∘ πc'= πe'(f×f')∘(g×g'), where πa maps a×a' to a.
    -- We have the two commuting diagrams from cxc' → d×d' and d×d' → e×e',
    -- which means f ∘ πc = πd ∘ (f×f') and f'∘πc' = πd'∘(f×f') (h₁)
    -- and g ∘ πd = πe ∘ (g×g') and g'∘πd' = πe'∘(g×g') (h₂).
    have cp_dp_comm := product_morphism_commutes cp dp f f',
    cases cp_dp_comm,
    have dp_ep_comm := product_morphism_commutes dp ep g g',
    cases dp_ep_comm,
    have h₁ : 𝒞.compose f cp.p₁ = 𝒞.compose dp.p₁ (pm cp dp f f') ∧ 𝒞.compose f' cp.p₂ = 𝒞.compose dp.p₂ (pm cp dp f f'),
    split,
    exact cp_dp_comm_left,
    exact cp_dp_comm_right,
    have h₂ : 𝒞.compose g dp.p₁ = 𝒞.compose ep.p₁ (pm dp ep g g') ∧ 𝒞.compose g' dp.p₂ = 𝒞.compose ep.p₂ (pm dp ep g g'),
    split,
    exact dp_ep_comm_left,
    exact dp_ep_comm_right,
    -- Now bringing these two together, we can prove that g ∘ f ∘ πc = πe (f×f')∘(g×g') (q₁)
    -- and g'∘ f'∘ πc'= πe'(f×f')∘(g×g') (q₂).
    have q₁ : 𝒞.compose g (𝒞.compose f cp.p₁) = 𝒞.compose ep.p₁ (𝒞.compose (pm dp ep g g') (pm cp dp f f')),
    rw h₁.left,    -- g ∘ πd ∘ (f×f') = πe (f×f')∘(g×g') via h₁
    rw 𝒞.assoc,    -- rewrite to (g ∘ πd) ∘ (f×f') = πe (f×f')∘(g×g') via associativity
    rw h₂.left,    -- (πe ∘ (g×g')) ∘ (f×f') = πe (f×f')∘(g×g') via h₂
    symmetry,      -- rewrite to πe (f×f')∘(g×g') = (πe ∘ (g×g')) ∘ (f×f') so it fits
    apply 𝒞.assoc, -- with the associativity rule for morphism composition and we're done.
    have q₂ : 𝒞.compose g' (𝒞.compose f' cp.p₂) = 𝒞.compose ep.p₂ (𝒞.compose (pm dp ep g g') (pm cp dp f f')),
    rw h₁.right,
    rw 𝒞.assoc,
    rw h₂.right,
    symmetry,
    apply 𝒞.assoc,
    -- This leaves us with applying the uniqueness property of e×e' and showing that (f×f')∘(g×g')
    -- fulfills (3.).
    apply ep.uu (product_morphism_bundle cp (𝒞.compose g f) (𝒞.compose g' f')) (𝒞.compose (pm dp ep g g') (pm cp dp f f')),
    split,
    rw ← q₁,
    rw 𝒞.assoc,
    refl,
    rw ← q₂,
    rw 𝒞.assoc,
    refl,
  end

-- Freely convert between unique arrows from c to a×b and
-- product morphisms from c×c to a×b.
lemma refl_ps_pm {𝒞 : category} {c a b : 𝒞} [has_all_products 𝒞]
(f : 𝒞.hom c a) (g : 𝒞.hom c b) : ps f g = 𝒞.compose (product_morphism f g) (mk_prod c) :=
  begin
    unfold ps,
    -- ps is the unique arrow from c to a×b via f and g, now showing that
    -- f×g ∘ (c → c×c, id id) is the same arrow
    rw ← (po a b).uu {x := c, x₁ := f, x₂ := g} (𝒞.compose (product_morphism f g) (mk_prod c)),
    simp,
    -- so we have to show that the left and right projections are equal to
    -- f and g respectively
    -- using our proof of product of morphisms commuting, we can change
    -- our goal to essentially proving f ∘ πc (via id) = f (likewise for g)
    have q := product_morphism_commutes (po c c) (po a b) f g,
    split,
    -- proving for f
    rw 𝒞.assoc,
    rw ← q.left,
    rw ← 𝒞.assoc, 
    rw simp_mk_prod_left,
    rw 𝒞.left_id,
    -- proving for g
    rw 𝒞.assoc,
    rw ← q.right,
    rw ← 𝒞.assoc, 
    rw simp_mk_prod_right,
    rw 𝒞.left_id,
  end

-- help lean some more
@[simp]
lemma simp_product_morphism {𝒞 : category} {c c' d d' : 𝒞} {cp : binary_product c c'} {dp : binary_product d d'}
{f f' : 𝒞.hom c d} {g g' : 𝒞.hom c' d'}
: f = f' ∧ g = g' → @product_morphism 𝒞 c d c' d' cp dp f g = product_morphism f' g' :=
  begin
    cc,
  end

lemma refl_product_morphism_pm {𝒞 : category} {c c' d d' : 𝒞} {cp : binary_product c c'} {dp : binary_product d d'}
{f : 𝒞.hom c d} {g : 𝒞.hom c' d'}
: product_morphism f g = pm cp dp f g :=
  begin
    unfold pm,
  end

-- Identical to product_of_composible_morphisms, but for use in categories where all products exist.
lemma refl_product_morphism_compose {𝒞 : category} [has_all_products 𝒞] {c c' d d' e e' : 𝒞}
(f : 𝒞.hom c d) (f' : 𝒞.hom c' d') (g : 𝒞.hom d e) (g' : 𝒞.hom d' e')
: 𝒞.compose (product_morphism g g') (@product_morphism 𝒞 c d c' d' (po c c') (po d d') f f')
= @product_morphism 𝒞 c e c' e' (po c c') (po e e') (𝒞.compose g f) (𝒞.compose g' f')  :=
  begin
    repeat { rw refl_product_morphism_pm },
    apply product_of_composible_morphisms,
  end

end category_theory