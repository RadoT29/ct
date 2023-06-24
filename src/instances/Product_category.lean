import category

open category_theory

-- C × D
-- product category of C and D
def Product (C D : category) : category :=
{
  -- Objects are ordered pairs (c, d)
  C₀ := C × D,
  
  -- Morphisms are ordered pairs of morphisms
  -- in C and in D
  hom := λ p p', (C.hom p.fst p'.fst) × (D.hom p.snd p'.snd),

  -- 𝟙(c, d) = (𝟙c, 𝟙d)
  id  := λ p, (𝟙C p.fst, 𝟙D p.snd),

  -- Composition composes each morphism in the pair in its
  -- original category.
  compose := λ {p q r} (g : (C.hom q.fst r.fst) × (D.hom q.snd r.snd))
                       (f : (C.hom p.fst q.fst) × (D.hom p.snd q.snd)), 
             ((C.compose g.fst f.fst), (D.compose g.snd f.snd)),

  -- We can use the proofs from function.comp.
  left_id :=
    begin
      intros,
      simp,
      rw C.left_id,
      rw D.left_id,
      simp,
    end,
  right_id :=
    begin
      intros,
      simp,
      rw C.right_id,
      rw D.right_id,
      simp,
    end,
  assoc :=
    begin
      intros,
      simp,
      rw C.assoc,
      rw D.assoc,
    end,
}

-- Some lemmas for use in proofs.

-- Both explicit and "standalone" representations of morphisms
-- are equivalent.
lemma refl_product_pair {C : category} {a b a' b' : C}
(f : C.hom a b) (f' : C.hom a' b') (h : (Product C C).hom (a, a') (b, b'))
: f = h.fst ∧ f' = h.snd → (f, f') = h :=
  begin
    intro q,
    rw q.left,
    rw q.right,
    simp,
  end

-- Compose each morphism in the pair in its original category,
-- but when we have our C×C morphism explicitly given as a pair.
lemma refl_product_compose {C : category} {a b c a' b' c' : C} 
(f : C.hom (b, b').fst (c, c').fst) (f' : C.hom (b, b').snd (c, c').snd)
(g : C.hom (a, a').fst (b, b').fst) (g' : C.hom (a, a').snd (b, b').snd)
: (Product C C).compose (f, f') (g, g') = (C.compose f g, C.compose f' g') :=
  begin
    refl,
  end