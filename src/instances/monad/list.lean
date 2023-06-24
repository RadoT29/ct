import instances.functors.List_functor
import monad

namespace category_theory

  def List.join {α} : List (List α) → List α
  | List.nil := List.nil
  | (List.cons l ls) := l ++ List.join ls

  def List.return {α} (a : α) : List α := List.cons a List.nil

  def List.monad : Monad List.functor :=
  {
    μ := {
      α := λ α, List.join,
      naturality_condition := begin
        intros,
        change (List.fmap f) ∘ List.join = List.join ∘ (List.fmap (List.fmap f)),
        apply funext,
        intro X,
        induction X,
        case List.nil {
          refl,
        },
        case List.cons {
          rw function.comp,
          change List.fmap f (List.join (List.cons X_head X_tail)) = (List.join ∘ List.fmap (List.fmap f)) (List.cons X_head X_tail),
          induction X_head,
          case List.nil {
            rw List.join,
            change (List.fmap f ∘ List.join) X_tail = (List.join ∘ List.fmap (List.fmap f)) (List.cons List.nil X_tail),
            rw X_ih,
            trivial,
          },
          case List.cons {
            rw List.join,
            rw List.merge,
            rw List.fmap,
            rw ←List.join,
            rw X_head_ih,
            trivial,
          },
        },
        done,
      end,
    },
    η := {
      α := λ α, List.return,
      naturality_condition := begin
        intros,
        trivial,
      end,
    },
    lu := begin
      intros,
      rw ID,
      rw right_unit_nt,
      rw nt_composition,
      rw bimap,
      rw nt_composition,
      apply nt_eq,
      simp,
      apply funext,
      intro X,
      rw Set.right_id,
      rw Set.right_id,
      rw List.functor.id X,
      change List.join ∘ (List.fmap List.return) = id,
      apply funext,
      intro x,
      induction x,
      case List.nil {
        refl,
      },
      case List.cons {
        rw function.comp,
        simp,
        rw List.fmap,
        rw List.join,
        change List.return x_head ++ (List.join ∘ (List.fmap List.return)) x_tail = List.cons x_head x_tail,
        rw x_ih,
        trivial,
      },
      done,
    end,
    ru := begin
      intros,
      rw ID,
      rw left_unit_nt,
      rw nt_composition,
      rw bimap,
      rw nt_composition,
      simp,
      apply funext,
      intro X,
      rw List.functor.id,
      change List.join ∘ List.return = id,
      apply funext,
      intro x,
      induction x,
      case List.nil {
        refl,
      },
      case List.cons {
        rw function.comp,
        simp,
        rw List.return,
        rw List.join,
        rw List.merge,
        rw ←List.join,
        rw ←List.return,
        change List.cons x_head ((List.join ∘ List.return) x_tail) = List.cons x_head x_tail,
        rw x_ih,
        trivial,
      },
      done,
    end,
    assoc := begin
      intros,
      rw assoc_nt,
      rw ID,
      rw nt_composition,
      rw bimap,
      rw nt_composition,
      rw bimap,
      rw nt_composition,
      simp,
      apply funext,
      intro X,
      change Set.compose List.join (Set.compose List.join (List.functor.map_hom (List.functor.map_hom (Set.id (List.functor.map_obj X))))) = Set.compose List.join (Set.compose (Set.compose (Set.id (List.functor.map_obj (List.functor.map_obj X))) (List.functor.map_hom List.join)) (List.functor.map_hom (List.functor.map_hom (List.functor.map_hom (Set.id X))))),
      change (List.functor.map_obj X) with (List X),
      rw List.functor.id,
      rw List.functor.id,
      rw Set.left_id,
      rw List.functor.id,
      change (List.functor.map_obj X) with (List X),
      rw List.functor.id,
      rw List.functor.id,
      rw Set.left_id,
      change (List.functor.map_obj (List X)) with (List (List X)),
      rw Set.right_id,
      change List.join ∘ List.join = List.join ∘ (List.fmap List.join),
      apply funext,
      intro x,
      induction x,
      case List.nil {
        refl,
      },
      case List.cons {
        rw function.comp,
        simp,
        rw List.join,
        induction x_head,
        case List.nil {
          rw List.merge,
          change List.join (List.join x_tail) with (List.join ∘ List.join) x_tail,
          rw x_ih,
          trivial,
        },
        case List.cons {
          rw List.merge,
          rw List.join,
          induction x_head_head,
          case List.nil {
            rw List.merge,
            rw x_head_ih,
            trivial,
          },
          case List.cons {
            rw List.merge,
            rw x_head_head_ih,
            trivial,
          },
        },
        done,
      },
    end,
  }

end category_theory
