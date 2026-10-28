import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Represented Subfunctor Range -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedSubfunctorRange

noncomputable section

/-! Exact ranges of represented subfunctors, including transport of a
representation along equality without losing the inclusion compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {M : Over S}

theorem representedSubfunctor_range (G : Subfunctor F) (e : yoneda.obj M ≅ G.toFunctor) :
    Subfunctor.range (e.hom ≫ G.ι) = G := by
  rw [Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top, Subfunctor.range_ι]

theorem subfunctor_representation_of_monic_range
    (t : yoneda.obj M ⟶ F) [Mono t] (G : Subfunctor F) (h : Subfunctor.range t = G) :
    ∃ e : yoneda.obj M ≅ G.toFunctor, e.hom ≫ G.ι = t := by
  subst G
  exact ⟨asIso (Subfunctor.toRange t), Subfunctor.toRange_ι t⟩

theorem representedSubfunctor_transport {G H : Subfunctor F} (h : G = H)
    (t : yoneda.obj M ⟶ F) (e : yoneda.obj M ≅ G.toFunctor) (he : e.hom ≫ G.ι = t) :
    ∃ e' : yoneda.obj M ≅ H.toFunctor, e'.hom ≫ H.ι = t := by
  subst H
  exact ⟨e, he⟩

theorem representedSubfunctor_restrict {Z : Over S}
    (G H : Subfunctor F) (e : yoneda.obj M ≅ G.toFunctor)
    (j : Z ⟶ M) [Mono j]
    (h : ∀ (T : Over S) (x : T ⟶ M),
      (e.hom.app (.op T) x).val ∈ H.obj (.op T) ↔ ∃ y : T ⟶ Z, y ≫ j = x) :
    ∃ e' : yoneda.obj Z ≅ (G ⊓ H).toFunctor,
      e'.hom ≫ (G ⊓ H).ι = yoneda.map j ≫ e.hom ≫ G.ι := by
  let t : yoneda.obj M ⟶ F := e.hom ≫ G.ι
  let k : yoneda.obj Z ⟶ F := yoneda.map j ≫ t
  have hk : Subfunctor.range k = G ⊓ H := by
    ext T v
    constructor
    · rintro ⟨z, rfl⟩
      change (e.hom.app T (z ≫ j)).val ∈ G.obj T ∧
        (e.hom.app T (z ≫ j)).val ∈ H.obj T
      exact ⟨(e.hom.app T (z ≫ j)).property, (h T.unop (z ≫ j)).mpr ⟨z, rfl⟩⟩
    · rintro ⟨hvG, hvH⟩
      let x := e.inv.app T ⟨v, hvG⟩
      have hx : (e.hom.app T x).val = v :=
        congrArg Subtype.val ((e.app T).inv_hom_id_apply ⟨v, hvG⟩)
      obtain ⟨z, hz⟩ := (h T.unop x).mp (hx.symm ▸ hvH)
      refine ⟨z, ?_⟩
      change (e.hom.app T (z ≫ j)).val = v
      rw [hz, hx]
  exact subfunctor_representation_of_monic_range k (G ⊓ H) hk

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RepresentedSubfunctorRange
