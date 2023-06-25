import .streams .final_coalgebra 

namespace category_theory

def pair_head_tail {α β : Type} : (stream α × stream β) → (α × β) × (stream α × stream β) :=
λ s, ((head s.1, head s.2), (tail s.1, tail s.2))

-- def zip {α β : Types.C₀} : (stream α × stream β) → stream (α × β) :=
-- unfolds (λ s, ((head s.1 × head s.2), (tail s.1 × tail s.2)))

def zip_coalgebra (α β : Type) : coalgebra (stream_functor (α × β)) :=
{
  object := stream α × stream β,
  morphism := λ x, pair_head_tail x,
}

def zips_homomorphism (α β : Type) : f_coalgebra_homomorphism (zip_coalgebra α β) (stream_coalgebra (α × β)) :=
{
  morphism := unfolds pair_head_tail,
  proof := by refl,
}

end category_theory