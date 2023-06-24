import category.category

namespace category_theory

  theorem double_square 
    {𝒞 : category}
    {X Y Z P Q R : 𝒞.C₀}
    {a : 𝒞.hom X Y}
    {b : 𝒞.hom Y Z}
    {c : 𝒞.hom P Q}
    {d : 𝒞.hom Q R}
    {e : 𝒞.hom X P}
    {f : 𝒞.hom Y Q}
    {g : 𝒞.hom Z R}
    :
    (𝒞.compose g b = 𝒞.compose d f) ∧
    (𝒞.compose f a = 𝒞.compose c e) →
    (𝒞.compose (𝒞.compose g b) a) = (𝒞.compose d (𝒞.compose c e))
    :=
    begin
      intros sq,
      cases sq with sq1 sq2,
      rw sq1,
      rw ←sq2,
      rw 𝒞.assoc,
    end

  theorem extend
    {𝒞 : category}
    {X Y Z : 𝒞.C₀}
    {f g : 𝒞.hom X Y}
    (h : 𝒞.hom Y Z)
    :
    f = g → 𝒞.compose h f = 𝒞.compose h g
    :=
    begin
      intros a,
      rw a,
    end

end category_theory
