import morphisms
import functors.composition
import natural_transformation.definition
import natural_transformation.composition

namespace category_theory

  def is_iso_nt {𝒞 𝒟 : category} {F G : 𝒞 ⇒ 𝒟} (α : F ≫ G) :=
    Π X : 𝒞, is_iso (α.α X)

  def assoc_nt {𝒞 𝒟 ℰ ℱ : category} (F : 𝒞 ⇒ 𝒟) (G : 𝒟 ⇒ ℰ) (H : ℰ ⇒ ℱ)
    : H • (G • F) ≫ (H • G) • F :=
    {
      α := λ X, H.map_hom (G.map_hom (F.map_hom (𝒞.id X))),
      naturality_condition := begin
        intros,
        rw [F.id, G.id],
        rw H.id (G.map_obj (F.map_obj X)),
        change ℱ.compose (H.map_hom (G.map_hom (F.map_hom f))) (ℱ.id (H.map_obj (G.map_obj (F.map_obj X)))) = ℱ.compose (H.map_hom (G.map_hom (F.map_hom (𝒞.id Y)))) ((H • G • F).map_hom f),
        rw ℱ.left_id,
        symmetry,
        rw [F.id, G.id, H.id],
        change ℱ.compose (ℱ.id (H.map_obj (G.map_obj (F.map_obj Y)))) (H.map_hom (G.map_hom (F.map_hom f))) = H.map_hom (G.map_hom (F.map_hom f)),
        rw ℱ.right_id,
      end
    }

  theorem assoc_nt_iso {𝒞 𝒟 ℰ ℱ : category} {F : 𝒞 ⇒ 𝒟} {G : 𝒟 ⇒ ℰ} {H : ℰ ⇒ ℱ}
    : is_iso_nt (assoc_nt F G H) :=
    begin
      intros,
      rw is_iso_nt,
      intros,
      rw is_iso,
      change
        ∃ (g : ℱ.hom (H.map_obj (G.map_obj (F.map_obj X))) (H.map_obj (G.map_obj (F.map_obj X)))),
          ℱ.compose g ((assoc_nt F G H).α X) = ℱ.id (H.map_obj (G.map_obj (F.map_obj X))) ∧
          ℱ.compose ((assoc_nt F G H).α X) g = ℱ.id (H.map_obj (G.map_obj (F.map_obj X))),
      existsi ℱ.id (H.map_obj (G.map_obj (F.map_obj X))),
      split,
      rw ℱ.right_id,
      rw assoc_nt,
      change H.map_hom (G.map_hom (F.map_hom (𝒞.id X))) = ℱ.id (H.map_obj (G.map_obj (F.map_obj X))),
      rw [F.id, G.id, H.id],
      rw ℱ.left_id,
      rw assoc_nt,
      change H.map_hom (G.map_hom (F.map_hom (𝒞.id X))) = ℱ.id (H.map_obj (G.map_obj (F.map_obj X))),
      rw [F.id, G.id, H.id],
      done,
    end

  def left_unit_nt {𝒞 𝒟 : category} (F : 𝒞 ⇒ 𝒟)
    : Id 𝒟 • F ≫ F :=
    {
      α := λ X, F.map_hom $ 𝒞.id X,
      naturality_condition := begin
        intros,
        rw ←F.comp,
        rw 𝒞.left_id,
        rw ←(𝒟.right_id $ F.map_hom f),
        rw ←F.id,
        trivial,
      end
    }

  theorem left_unit_nt_iso {𝒞 𝒟 : category} (F : 𝒞 ⇒ 𝒟)
    : is_iso_nt $ left_unit_nt F :=
    begin
      intros,
      rw is_iso_nt,
      intros,
      rw is_iso,
      existsi (F.map_hom (𝒞.id X)),
      split,
      rw F.id,
      rw 𝒟.right_id,
      rw left_unit_nt,
      change F.map_hom (𝒞.id X) = 𝒟.id (F.map_obj X),
      rw F.id,
      rw F.id,
      rw 𝒟.left_id,
      rw left_unit_nt,
      change F.map_hom (𝒞.id X) = 𝒟.id (F.map_obj X),
      rw F.id,
      done,
    end

  def right_unit_nt {𝒞 𝒟 : category} (F : 𝒞 ⇒ 𝒟)
    : F • Id 𝒞 ≫ F :=
    {
      α := λ X, F.map_hom $ 𝒞.id X,
      naturality_condition := begin
        intros,
        rw F.id X,
        rw 𝒟.left_id (F.map_hom f),
        symmetry,
        rw F.id Y,
        change 𝒟.compose (𝒟.id (F.map_obj Y)) (F.map_hom f) = F.map_hom f,
        rw 𝒟.right_id,
        done,
      end
    }

  theorem right_unit_nt_iso {𝒞 𝒟 : category} (F : 𝒞 ⇒ 𝒟)
    : is_iso_nt $ right_unit_nt F :=
    begin
      intros,
      rw is_iso_nt,
      intros,
      rw is_iso,
      rw right_unit_nt,
      existsi (F.map_hom (𝒞.id X)),
      split,
      change 𝒟.compose (F.map_hom (𝒞.id X)) (F.map_hom (𝒞.id X)) = 𝒟.id (F.map_obj X),
      rw F.id,
      rw 𝒟.left_id,
      change 𝒟.compose (F.map_hom (𝒞.id X)) (F.map_hom (𝒞.id X)) = 𝒟.id (F.map_obj X),
      rw F.id,
      rw 𝒟.left_id,
      done,
    end

end category_theory
