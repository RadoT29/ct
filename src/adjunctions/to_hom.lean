import functors
import adjunctions.homset
import adjunctions.unit_counit

namespace category_theory

-- Mac Lane pg. 82, Theorem 1 (6), (7)
def adjunction_to_hom {𝒞 𝒟} {L : 𝒞 ⇒ 𝒟} {R} (a : adjunction_unit L R) : adjunction_hom L R :=
{
  -- φ(k)  = R k ∘ η c
  φ  := λ {c d} (k : 𝒟.hom (L c) d), 𝒞.compose (R.map_hom k) (a.η.α c),
  -- φr(h) = ε d ∘ L h
  φr := λ {c d} (h : 𝒞.hom c (R d)), 𝒟.compose (a.ε.α d) (L.map_hom h),
  sect := λ {c d} (h : 𝒞.hom c (R d)),
    begin
      simp,
      -- ⊢ R (ε d ∘ L h) ∘ η c = h
      rw R.comp (L.map_hom h) (a.ε.α d), -- un-distribute R
      -- ⊢ (R ε d ∘ R L h) ∘ η c = h
      rw ← 𝒞.assoc,                      -- change parantheses
      -- ⊢ R ε d ∘ (R L h ∘ η c) = h
      erw a.η.naturality_condition,      -- using η naturality
      -- ⊢ R ε d ∘ (η R d ∘ h) = h
      erw 𝒞.assoc,                       -- change parantheses again for Lean
      -- ⊢ (R ε d ∘ η R d) ∘ h = h
      erw a.id_R,
      -- ⊢ h = h - well, not actually this, but equivalent to it
      erw 𝒞.right_id,
      refl,
    end,
  retr := λ {c d} (k : 𝒟.hom (L c) d),
      begin
      simp,
      -- analogous (dual!!) to section
      rw L.comp,
      rw 𝒟.assoc,
      erw ← a.ε.naturality_condition,
      erw ← 𝒟.assoc,
      erw a.id_L,
      erw 𝒟.left_id, 
      refl,
      end,
  naturality_c :=
    begin
      intros,
      rw ← 𝒞.assoc,
      erw ← a.η.naturality_condition,
      rw 𝒞.assoc,
      erw ← R.comp,
    end,
  naturality_d :=
    begin
      intros,
      rw 𝒞.assoc,
      rw R.comp,
    end,
  -- dual to naturality_d
  naturality_cr :=
    begin
      intros,
      rw ← 𝒟.assoc,
      rw L.comp,
    end,
  -- dual to naturality_c
  naturality_dr :=
    begin
      intros,
      rw 𝒟.assoc,
      erw a.ε.naturality_condition,
      rw ← 𝒟.assoc,
      erw L.comp,
      refl,
    end,
}

end category_theory