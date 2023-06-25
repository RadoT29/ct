-- Example
-- Stream
import .coalgebra ..instances.types_category
namespace category_theory

universe u

inductive binary_tree (α : Type u) : Type u
| cons (value : α) (left : binary_tree) (right: binary_tree) : binary_tree

def binary_tree.value {α : Type*} (s : binary_tree α) : α :=
match s with
| binary_tree.cons v _ _ := v
end

def binary_tree.left {α : Type*} (s : binary_tree α) : binary_tree α :=
match s with
| binary_tree.cons _ l _ := l
end

def binary_tree.right {α : Type*} (s : binary_tree α) : binary_tree α :=
match s with
| binary_tree.cons _ _ r := r
end


def binary_tree_functor (α : Type*) : functor Types Types :=
{
  map_obj := λ X, α × X × X,
  map_hom := 
    begin
      intros X Y f,
      intro p,
      cases p with a x,
      cases x with x1 x2,
      exact (a, f x1, f x2)
    end,
  id := 
    begin
      intro X,
      simp,
      funext x,
      cases x,
      cases x_snd,
      refl
    end,
  comp := 
    begin
      intros X Y Z f g,
      simp,
      funext p,
      cases p with a x,
      cases x with x1 x2,
      simp,
      refl
    end
}

def tree_coalgebra {α : Types.C₀} : coalgebra (binary_tree_functor α) :=
{
  object := binary_tree α,
  morphism := λ s, (s.value, s.left, s.right)
}

end category_theory