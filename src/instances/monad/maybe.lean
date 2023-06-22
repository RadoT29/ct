import instances.functors.Maybe_functor
import monad

namespace category_theory

  notation (name := none) ∅ := Maybe.none

  def Maybe.join {α : Type*} : Maybe (Maybe α) → Maybe α
  | ∅ := ∅
  | (Maybe.some x) := x

  def Maybe.return {α : Type*} (x : α) : Maybe α := Maybe.some x

  def monad_maybe : Monad MaybeFunctor :=
  {
    μ := {
      α := λ X, Maybe.join,
      naturality_condition := begin
        intros,
        change (Maybe.fmap f) ∘ Maybe.join = Maybe.join ∘ (Maybe.fmap (Maybe.fmap f)), 
        apply funext,
        intro x,
        cases x,
        trivial,
        trivial,
        done,
      end,
    },
    η := {
      α := λ X, Maybe.return,
      naturality_condition := begin
        intros,
        -- change (Maybe.fmap f) ∘ Maybe.return = Maybe.return ∘ f,
        -- change (Maybe.fmap f) ∘ Maybe.some = Maybe.some ∘ f,
        trivial,
        done,
      end,
    },
    ru := begin
      intros,
      rw [nt_composition, bimap],
      symmetry,
      rw nt_composition,
      rw ID,
      rw left_unit_nt,
      apply nt_eq,
      change (λ X, Set.compose (Set.id (MaybeFunctor.map_obj X)) (MaybeFunctor.map_hom (Set.id X))) = (λ (X : ↥Set), Set.compose (Maybe.join) (Set.compose (Maybe.return) ((Id Set).map_hom (Set.id (MaybeFunctor.map_obj X))))),
      apply funext,
      intro X,
      rw MaybeFunctor.id,
      trivial,
      done,
    end,
    lu := begin
      intros,
      rw [nt_composition, bimap],
      symmetry,
      rw nt_composition,
      rw ID,
      rw right_unit_nt,
      apply nt_eq,
      change (λ (X : ↥Set), Set.compose (Set.id (MaybeFunctor.map_obj X)) (MaybeFunctor.map_hom (Set.id X))) = (λ (X : ↥Set), Set.compose (Maybe.join) (Set.compose (Set.id (MaybeFunctor.map_obj (MaybeFunctor.map_obj X))) (MaybeFunctor.map_hom (Maybe.return)))),
      apply funext,
      intro X,
      rw MaybeFunctor.id,
      rw Set.left_id,
      change Set.id (MaybeFunctor.map_obj X) = Set.compose Maybe.join (Set.compose (Set.id (Maybe (Maybe X))) (MaybeFunctor.map_hom Maybe.return)),
      rw Set.right_id,
      change id = Maybe.join ∘ (Maybe.fmap Maybe.return),
      apply funext,
      intro x,
      cases x,
      trivial,
      trivial,
      done,
    end,
    assoc := begin
      intros,
      rw assoc_nt,
      rw ID,
      rw [nt_composition, bimap],
      symmetry,
      rw [nt_composition, bimap],
      rw nt_composition,
      apply nt_eq,
      change (λ (X : ↥Set), Set.compose (Maybe.join) (Set.compose (Set.compose (Set.id (Maybe (Maybe X))) (MaybeFunctor.map_hom (Maybe.join))) (MaybeFunctor.map_hom (MaybeFunctor.map_hom (MaybeFunctor.map_hom (Set.id X)))))) = (λ X, Set.compose (Maybe.join) (Set.compose (Maybe.join) (MaybeFunctor.map_hom (MaybeFunctor.map_hom (Set.id (MaybeFunctor.map_obj X)))))),
      apply funext,
      intro X,
      rw Set.right_id,
      rw MaybeFunctor.id,
      rw MaybeFunctor.id,
      rw MaybeFunctor.id,
      rw Set.left_id,
      rw Set.left_id,
      apply funext,
      intro x,
      cases x,
      trivial,
      trivial,
      done,
    end,
  }

end category_theory
