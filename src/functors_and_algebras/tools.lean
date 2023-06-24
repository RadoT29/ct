import category
import functors.functor
import functors_and_algebras.f_algebra
import functors_and_algebras.algebra_category
namespace category_theory

universes u v

-- α + β
inductive Either (α : Type u) (β : Type v)
  | left : α → Either
  | right : β → Either

-- α ⨯ β
inductive Pair (α : Type u) (β : Type v)
  | pair : α → β → Pair

-- The singleton type
inductive Singleton
  | star : Singleton


notation `⟨` lhs `,` rhs `⟩` := Pair.pair lhs rhs
notation `⋆` := Singleton.star

def fst {α : Type u} {β : Type v} : Pair α β → α
| ⟨x, _⟩ := x

def snd {α : Type u} {β : Type v} : Pair α β → β
| ⟨_, y⟩ := y

-- Proof that a pair P is equal to a pair constructed using the first and second element of P
lemma pair_eq {α : Type u} {β : Type v}
  : ∀P : Pair α β, ⟨fst P, snd P⟩ = P
| ⟨x, y⟩ :=
  begin
    simp [fst, snd]
  end

-- Definition of an initial object, which enforces the existance of a catamorphism
structure initial (C : category) := 
  (object : C.C₀)
  (exist_morph : Π (X : C.C₀), C.hom object X)
  (is_unique : ∀ {X : C.C₀} (f : C.hom object X), f = exist_morph X)

-- Definition of a isomorphism, which holds the inverse and properties.
class isomorphism {C : category} {N M : C.C₀} (hom : C.hom N M) :=
  (inverse : C.hom M N)
  (idl : C.compose hom inverse = C.id M)
  (idr : C.compose inverse hom = C.id N)

-- Proof that the inverse of an isomorphism is unique.
lemma inverse_uniqueness {C : category} {A B : C.C₀} : 
  ∀ (f : C.hom A B) (g h : isomorphism f), g.inverse = h.inverse :=
begin
  intros,
  -- We can rewrite g.inverse by using the fact that g.inverse ∘ Id = g.inverse
  rw [←C.left_id g.inverse],
  -- Now we can apply the fact that Id = f ∘ h.inverse
  rw [←h.idl],
  -- We currently have that g.inverse ∘ (f ∘ h.inverse). In order to use the fact that g.inverse ∘ f = Id
  -- we rewrite using the associativity property of category C
  rw [C.assoc],
  -- Apply g.inverse ∘ f = Id
  rw [g.idr],
  -- Apply that Id ∘ h.inverse = h.inverse
  rw [C.right_id],
end 

-- inductive List (α: Type) : Type
--   | nil : List
--   | cons (head: α) (tail: List) : List

-- inductive Maybe (α : Type)
--   | none : Maybe
--   | some : α → Maybe

inductive BTree (α : Type)
  | leaf (el : α) : BTree
  | node (l :BTree) (r : BTree) : BTree

end category_theory