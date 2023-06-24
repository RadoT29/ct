import .streams .final_coalgebra 

namespace category_theory

def succ_pair : ℕ → ℕ × ℕ := λ n, (n, n + 1)

def nat_coalgebra : coalgebra (stream_functor ℕ) :=
{
  object := ℕ,
  morphism := succ_pair
}

def nats_homomorphism : f_coalgebra_homomorphism nat_coalgebra (stream_coalgebra ℕ) :=
{
  morphism := unfolds succ_pair,
  proof := by refl,
}

end category_theory