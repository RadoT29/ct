import universal_properties.universal_properties
import instances.Set_category

namespace category_theory

-- The empty set is an initial object in the Set category
lemma empty_set_initial_in_Set : is_initial Set empty :=
begin
  intros B f g,
  funext x,
  cases x, -- There are no elements in the empty set, so we can use cases to handle all possible cases (i.e., none)
end

def initial_object_in_Set : initial_object Set :=
{
  object := empty,
  property := empty_set_initial_in_Set
}


-- The singleton (unit) set is a terminal object in the Set category
lemma singleton_set_terminal_in_Set : is_terminal Set unit :=
begin
  intros A f g,
  funext x,
  apply subsingleton.elim (f x) (g x), -- Using the subsingleton property to conclude f x = g x
end

def terminal_object_in_Set : terminal_object Set :=
{
  object := unit,
  property := singleton_set_terminal_in_Set,
}


-- The cartesian product A × B along with its projection functions forms a binary product in the Set category
lemma cartesian_with_projections_binary_product_in_Set (A B : Set.C₀) : is_binary_product Set (A × B) (λ p, p.1) (λ p, p.2) :=
begin
  intros Q q₁ q₂,

  -- Define a product morphism f
  let f : Q → A × B := λ x, (q₁ x, q₂ x),

  -- Define and prove lemmas proj₁ and proj₂
  -- They state that for any x ∈ Q, applying the projection functions to (f x) yield (q₁ x) and (q₂ x), respectively
  -- This is true because (f x) is defined as (q₁ x, q₂ x)
  have proj₁ : ∀ (x : Q), (λ p : A × B, p.1) (f x) = q₁ x,
  {
    intro x,
    simp [f],
  },
  have proj₂ : ∀ (x : Q), (λ p : A × B, p.2) (f x) = q₂ x,
  {
    intro x,
    simp [f],
  },

  -- Prove that f is the unique product morphism
  -- This can be done by splitting the goal into two subgoals and proving them
  -- The first subgoal states that f is indeed a valid product morphism
  -- The second subgoal states that f is the only valid product morphism
  existsi f,
  split,

  -- Prove the first subgoal
  {
    split,

    -- Prove that the diagram commutes to the left
    -- That is, applying the projection function π₁ to f results in q₁
    {
      apply funext,
      intro x,
      exact (proj₁ x),
    },
    
    -- Prove that the diagram commutes to the right
    -- That is, applying the projection function π₂ to f results in q₂
    {
      apply funext,
      intro x,
      exact (proj₂ x),
    },
  },

  -- Prove the second subgoal
  {
    intros g H,
    apply funext,
    intro x,
    cases H with H₁ H₂,

    -- Define and prove lemmas H₁' and H₂'
    -- They state that for any x ∈ Q, applying the projection functions to (g x) yield (q₁ x) and (q₂ x), respectively
    have H₁' : (λ (p : A × B), p.1) (g x) = q₁ x,
    {
      rw ←H₁,
      refl,
    },
    have H₂' : (λ (p : A × B), p.2) (g x) = q₂ x,
    {
      rw ←H₂,
      refl,
    },

    -- Use H₁' and H₂' to finish the proof
    simp [f],
    rw ←H₁', 
    rw ←H₂', 
    simp [H₁', H₂'],
  },
end

def binary_product_in_Set (A B : Set.C₀) : binary_product Set A B :=
{
  P := A × B, 
  π₁ := λ p, p.1, 
  π₂ := λ p, p.2, 
  property := cartesian_with_projections_binary_product_in_Set A B, 
}


-- The disjoint union A ⊕ B along with its inclusion maps forms a binary coproduct in the Set category
lemma union_with_inclusions_binary_coproduct_in_Set (A B : Set.C₀) : is_binary_coproduct Set (A ⊕ B) sum.inl sum.inr :=
begin
  intros D i₁ i₂,

  -- Define the coproduct morphism
  let f : (A ⊕ B) → D := λ x, sum.cases_on x i₁ i₂,

  -- Define and prove lemmas inl and inr
  -- They state that for any x ∈ A, applying f to the inclusion functions applied to x yield (i₁ x) and (₂ x), respectively
  -- This is true because (f x) maps (sum.inl x) to i₁ x and (sum.inr x) to i₂ x
  have inl : ∀ (x : A), f (sum.inl x) = i₁ x,
  {
    intro x,
    simp [f],
  },
  have inr : ∀ (x : B), f (sum.inr x) = i₂ x,
  {
    intro x,
    simp [f],
  },

  -- Prove that f is the unique coproduct morphism
  -- This can be done by splitting the goal into two subgoals and proving them
  -- The first subgoal states that f is indeed a valid coproduct morphism
  -- The second subgoal states that f is the only valid coproduct morphism
  existsi f,
  split,
  
  -- Prove the first subgoal
  {
    split,
   
    -- Prove that the diagram commutes to the left
    -- That is, applying f to the inclusion function ι₁ results in i₁
    {
      apply funext,
      intro x,
      exact (inl x),
    },

    -- Prove that the diagram commutes to the right
    -- That is, applying f to the inclusion function ι₂ results in i₂
    {
      apply funext,
      intro x,
      exact (inr x),
    },
  },
  
  -- Prove the second subgoal
  {
    intros g H,
    apply funext,
    intro x,
    cases x,

    -- Prove the case where x = sum.inl x
    {
      change (g (sum.inl x)) with ((λ (p : A ⊕ B), g p) (sum.inl x)),
      
      -- Define and prove lemma H₁'
      -- It states that for any x ∈ A, applying g to (sum.inl x) yields (i₁ x)
      have H₁' : (λ (p : A ⊕ B), g p) (sum.inl x) = i₁ x,
      {
        rw ←H.1,
        refl,
      },
      rw H₁',
    },

    -- Prove the case where x = sum.inr x
    {
      change (g (sum.inr x)) with ((λ (p : A ⊕ B), g p) (sum.inr x)),
      
      -- Define and prove lemma H₂'
      -- It states that for any x ∈ A, applying g to (sum.inr x) yields (i₂ x)
      have H₂' : (λ (p : A ⊕ B), g p) (sum.inr x) = i₂ x,
      {
        rw ←H.2,
        refl,
      },
      rw H₂',
    },
  },
end

def binary_coproduct_in_Set (A B : Set.C₀) : binary_coproduct Set A B :=
{
  Cₚ := A ⊕ B, 
  ι₁ := sum.inl,
  ι₂ := sum.inr,
  property := union_with_inclusions_binary_coproduct_in_Set A B,
}

end category_theory