-- Category of coalgebras
import .coalgebra


namespace category_theory

def coalgebra_category {C: category} (F : functor C C) : category :=
{ C₀ := coalgebra F,
  hom := λ A B, f_coalgebra_homomorphism A B,
  id := λ A, {
    morphism := C.id A.object,
    proof := begin
      intros,
      simp [F.id, C.right_id, C.left_id],
    end
  },
  compose := λ X Y Z g f, {
    morphism := C.compose g.morphism f.morphism,
    proof := begin
      intros,
      rw C.assoc,
      rw g.proof,
      rw ← C.assoc,
      rw f.proof,
      rw C.assoc,
      repeat { rw f.proof },
      rw functor.comp,
    end
  },

  left_id :=
    begin
      intros,
      simp [functor.id, C.left_id],
      cases f,
      refl,
    end,
  right_id :=
    begin
      intros,
      simp [functor.id, C.right_id],
      cases f,
      refl,
    end,
  assoc :=
    begin
      intros,
      simp [C.assoc],
    end,
}


end category_theory