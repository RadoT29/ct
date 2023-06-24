import category
import functors

namespace category_theory 

structure natural_transformation {𝒞 𝒟 : category} (F G : 𝒞 ⇒ 𝒟) :=
  (α : Π (X : 𝒞) , 𝒟.hom (F.map_obj X) (G.map_obj X))
  (naturality_condition : ∀ {X Y : 𝒞} (f : 𝒞.hom X Y), 
    𝒟.compose (G.map_hom f) (α X)  = 
    𝒟.compose (α Y) (F.map_hom f)
  )

  -- notation
  infixr `≫`:75 := natural_transformation

  theorem nt_eq {𝒞 𝒟 : category} {F G : 𝒞 ⇒ 𝒟} (α β : F ≫ G) : 
    α.α = β.α → α = β :=
    begin
      intro h,
      cases α,
      cases β,
      congr,
      exact h,
    end


end category_theory
