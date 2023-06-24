def stream (α : Type*) := nat → α

def cons {α : Type*} (a : α) (s : stream α) : stream α
| nat.zero       := a
| (nat.succ n) := s n

def head {α : Type*} (s : stream α) : α := s 0

def tail {α : Type*} (s : stream α) : stream α := λ i, s (nat.succ i)

def unfolds {α β : Type*} : (α → β × α) → (α) → stream β
| f a nat.zero := (f a).1
| f a (nat.succ n) := unfolds f (f a).2 (n)