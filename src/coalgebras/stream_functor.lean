import ..functors.functor ..instances.types_category 

namespace category_theory

def stream_functor (α : Type) : functor Types Types :=
{
  map_obj := λ X, α × X,
  map_hom := λ X Y f, λ p, (p.fst, f p.snd),
  id := 
    begin
      intro X,
      funext x,
      cases x,
      refl
    end,
  comp := 
    begin
      intros X Y Z f g,
      funext p,
      cases p with a x,
      simp,
      refl
    end
}

end category_theory