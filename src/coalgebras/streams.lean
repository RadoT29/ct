-- Example
-- Stream
import .final_coalgebra ..instances.types_category ..universal_properties .stream_dt 

universe u

namespace category_theory

def stream_functor (α : Type*) : functor Types Types :=
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

def stream_coalgebra (α : Types.C₀) : coalgebra (stream_functor α) :=
-- def stream_coalgebra (α : Types.C₀) : (coalgebra_category (stream_functor α)).C₀ :=
{
  object := stream α,
  morphism := λ s, (head s, tail s)
}

lemma unfold_head {S : Types.C₀} {f : Types.hom S ((stream_functor S).map_obj S)} {x:S} :
  head (unfolds f x) = (f x).fst :=
begin
  -- unfold unfolds,
  -- simp [head],
  refl,
end

axiom unfold_tail {α β  : Types.C₀} {f : α → β × α} {x:α} :
  tail (unfolds f x) = unfolds f (f x).snd

-- lemma unfold_tail {α β  : Types.C₀} {f : α → β × α} {x:α} :
--   tail (unfolds f x) = unfolds f (f x).snd :=
-- begin
--   -- unfold unfolds,
--   -- simp [unfolds, tail, corec', corec, map, nth],
--   -- simp [function.comp],
--   -- simp [iterate],
--   -- funext,
  
--   refl,

-- end

def unfold_homomorphism  {α : Types.C₀} (A : coalgebra (stream_functor α)) : f_coalgebra_homomorphism A (stream_coalgebra α) := 
{
  morphism := unfolds A.morphism,
  proof := 
  begin
    funext x,

    have simp_left : Types.compose (stream_coalgebra α).morphism (unfolds A.morphism) x
    = (stream_coalgebra α).morphism ((unfolds A.morphism) x) := begin refl end,
    rw simp_left,

    have simp_right : Types.compose ((stream_functor α).map_hom (unfolds A.morphism)) A.morphism x =
    ((stream_functor α).map_hom (unfolds A.morphism)) (A.morphism x)
     := by refl,
    rw simp_right,
    
    -- -- funext n,
    -- cases x,
    -- cases (A.morphism x) with a s,


    have h1 : (stream_coalgebra α).morphism (unfolds A.morphism x) 
    = ((A.morphism x).fst, tail (unfolds A.morphism x))  := by refl,
    rw [h1],

    -- have h2 : (head (unfolds A.morphism x), tail (unfolds A.morphism x))
    --   = ((A.morphism x).fst, tail (unfolds A.morphism x)) := by refl,
    -- rw [h2],

    -- unfold tail,
    -- cases (A.morphism x) with a s,
    -- simp,
    

    have h3 : (stream_functor α).map_hom (unfolds A.morphism) (A.morphism x)
      = ((A.morphism x).fst, (unfolds A.morphism (A.morphism x).snd)) := by refl,
    rw [h3],

    rw unfold_tail,

  end,
} 

-- Stronger induction hypothesis that states that the nth element of the 
-- stream resultant of the hypothetical morphism is the nth unfold of the 
-- hypothetical morphism. This is used to prove the uniqueness of the unfold 
-- anamorphism. It is necessary since the induction tactic only induces the n-index
-- and not the x object. Here we use a stroger hypothesis to a general x
-- axiom inductive_hypothesis {α : Types.C₀} {A : (coalgebra_category (stream_functor α)).C₀} 
--   {f_morphism : Types.hom A.object (stream_coalgebra α).object } 
--   {x : A.object} {n : ℕ} :
--     f_morphism x n  = unfolds A.morphism x n

def proof_stream_is_final {α : Types.C₀} : final_coalgebra (stream_functor α) := 
{
  obj := stream_coalgebra α,
  anamorphism := unfold_homomorphism,
  unique := 
    begin
      intros A f,
      rw unfold_homomorphism,
      cases f,

      have h : f_morphism = unfolds A.morphism :=
      begin
        funext x,
        funext n,

        induction n with n ih,
        -- induction n using nat.strong_induction_on with n ih generalizing x,
        
        case nat.zero{ -- Case n = 0
          rw unfolds,
          have h : f_morphism x 0 = (Types.compose prod.fst (Types.compose (stream_coalgebra α).morphism f_morphism)) x := by refl,
          simp [h],
          rw [f_proof],
          refl,
        },
        case nat.succ{ -- Case n > 0
          rw [unfolds],
          -- unfold unfolds at IH,
          -- rw [IH],
          
          have h : f_morphism x n.succ = (Types.compose prod.snd (Types.compose (stream_coalgebra α).morphism f_morphism)) x n := by refl,
          simp [h],
          rw [f_proof],

          have h : Types.compose prod.snd (Types.compose ((stream_functor α).map_hom f_morphism) A.morphism) x n
            = f_morphism (A.morphism x).snd n := by refl,
          simp [h],
          
          -- have test: unfolds A.morphism x n.succ = unfolds A.morphism (A.morphism x).snd (n) := by refl,
          -- refl,
          -- rw IH,
          cases (A.morphism x) with a s,
          simp,
          
          -- exact inductive_hypothesis,
          sorry,
        },
      end,
      simp [h],
    end
}

end category_theory