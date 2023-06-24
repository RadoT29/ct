import functors
import adjunctions.homset
import adjunctions.unit_counit

namespace category_theory

-- Convert an adjunction defined via homset bijection to unit-counit adjunction
def adjunction_hom_to_unit {𝒞 𝒟} {L : 𝒞 ⇒ 𝒟} {R} (a : adjunction_hom L R)
: adjunction_unit L R :=
{
  -- the unit η can be constructing by using φ c on the identity morphism for L c,
  -- mapping 𝒟(L c, L c) to 𝒞(c, R (L c)), which is exactly a mapping made by a 
  -- natural transformation from Id C to R⬝L.
  η := {
    -- we construct the map as explained above
    α := λ c, by exact a.φ (𝒟.id (L c)),
    -- and prove that it preserves the naturality condition
    naturality_condition := 
      begin
        intros c' c h,
        erw a.naturality_d,            -- use naturality in 𝒟
        erw 𝒟.left_id,                 -- eliminate id
        rw ← 𝒟.right_id (L.map_hom h), -- introduce id on other side
        erw a.naturality_c,            -- use naturality in 𝒞
        refl,
      end,
  },
  -- the counit ε can be constructed in a similar manner to the unit, by taking the
  -- inverse of the φ bijection (φr) and mapping 𝒞(R d, R d) to 𝒟(L (R d), d).
  -- (a natural transformation from L⬝R to Id D).
  ε := {
    α := λ d, by exact a.φr (𝒞.id (R d)),
    -- proof is analogous (also dual) to η
    naturality_condition :=
      begin
        intros d d' g,
        apply symm,
        erw a.naturality_cr,
        erw 𝒞.right_id,
        rw ← 𝒞.left_id (R.map_hom g),
        erw adjunction_hom.naturality_dr,
        refl,
      end,
  },
  -- All that is left to do is prove the triangle identities.
  id_L :=
    begin
      intro c,
      simp,
      erw a.naturality_cr,
      erw 𝒞.right_id,
      apply a.retr,
    end,
  id_R := 
    begin
      intro d,
      simp,
      erw a.naturality_d,
      erw 𝒟.left_id,
      apply a.sect,
    end,
}

end category_theory