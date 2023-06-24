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

end category_theory