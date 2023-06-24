import functors.functor
import category

namespace category_theory

  theorem keep_equation {𝒞 𝒟 : category} (F : 𝒞 ⇒ 𝒟) :
    ∀ {X Y : 𝒞} (f g : 𝒞.hom X Y), f = g → F.map_hom f = F.map_hom g :=
  begin
    intros X Y f g heq,
    rw heq,
  end

end category_theory
