-- The functor from the category of posets to the category of sets
import category
import functors
import instances.Pos_category
import instances.Set_category

open category_theory

def poset_to_set : functor Pos Set :=
{
  map_obj := λ x, x.memb,
  map_hom := λ x y f, f.val,
  id := begin intros, trivial, end,
  comp := begin intros, trivial, end,
}
