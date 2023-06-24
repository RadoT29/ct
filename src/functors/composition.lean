import functors.functor

namespace category_theory

  -- Creates the composition of two functors.
  def composition_functor {𝒞 𝒟 ℰ : category} (G : 𝒟 ⇒ ℰ) (F : 𝒞 ⇒ 𝒟) : 𝒞 ⇒ ℰ :=
  {
    map_obj := λ X : 𝒞, G.map_obj (F.map_obj X),
    map_hom := λ X Y : 𝒞, λ f, G.map_hom (F.map_hom f),
    id :=
      begin
        intro,
        rw F.id,
        rw G.id,
      end,
    comp :=
      begin
        intros,
        rw F.comp,
        rw G.comp,
      end,
  }
  -- notation
  infixr `•`:90 := composition_functor

  def functor_comp_assoc {𝒞 𝒟 ℰ ℱ : category} : ∀ (F : 𝒞 ⇒ 𝒟) (G : 𝒟 ⇒ ℰ) (H : ℰ ⇒ ℱ),
    (H • G) • F = H • (G • F) := begin
      intros,
      trivial,
    end

end category_theory
