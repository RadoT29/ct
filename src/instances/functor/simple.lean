import category
import functors

open category_theory

-- Type with only two objects
inductive duo : Type
| A : duo 
| B : duo

-- Arrows in both directions and also as id.
def fun_duo : duo → duo → Prop
| _ _ := true

-- Duo type as category with fun
def duo_as_cat : category :=
{
  C₀ := duo,
  hom := fun_duo,
  id := begin intro, trivial, end,
  compose := begin intros, trivial, end,
  left_id := begin intros, trivial, end,
  right_id := begin intros, trivial, end,
  assoc := begin intros, trivial, end,
}

-- Function to map A to B and B to A
def switch : duo → duo
| duo.A := duo.B
| _ := duo.A

-- Switch function as functor on the Duo category.
def duo_as_functor : functor duo_as_cat duo_as_cat :=
{
  map_obj := switch,
  map_hom := begin intros, trivial, end,
  comp := begin intros, trivial, end,
  id := begin intros, trivial, end,
}

