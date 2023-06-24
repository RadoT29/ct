import category

namespace category_theory

structure functor (𝒞 𝒟 : category) :=
  (map_obj : 𝒞 → 𝒟)
  (map_hom : Π {X Y : 𝒞} (f : 𝒞.hom X Y), 𝒟.hom (map_obj X) (map_obj Y))
  (id : ∀ (X : 𝒞), map_hom (𝒞.id X) = 𝒟.id (map_obj X))
  (comp : ∀ {X Y Z : 𝒞} (f : 𝒞.hom X Y) (g : 𝒞.hom Y Z), map_hom (𝒞.compose g f) = 𝒟.compose (map_hom g) (map_hom f))

  -- notation
  infixr `⇒`:80 := functor

  -- Coercion from functor to function.
  -- This only works for the object mapping (map_obj!).
  -- For morphism mapping use functor_map defined below.
  instance coe_functor_obj {𝒞 𝒟 : category} : has_coe_to_fun (functor 𝒞 𝒟) (λ f, 𝒞 → 𝒟) :=
  {
    coe := λ f, f.map_obj
  }

  def functor_map {𝒞 𝒟 : category} (F: functor 𝒞 𝒟) {X Y : 𝒞} (f : 𝒞.hom X Y) :  𝒟.hom (F.map_obj X) (F.map_obj Y) := F.map_hom f

  def is_full {𝒞 𝒟 : category} (F: functor 𝒞 𝒟) :=
    ∀ {X Y : 𝒞} (g : 𝒟.hom (F.map_obj X) (F.map_obj Y)), ∃ (f : 𝒞.hom X Y), (F.map_hom f) = g

  def is_faithful {𝒞 𝒟 : category} (F: functor 𝒞 𝒟) :=
    ∀ {X Y : 𝒞} {f g : 𝒞.hom X Y} (h : functor_map F f = functor_map F g), f = g

end category_theory
