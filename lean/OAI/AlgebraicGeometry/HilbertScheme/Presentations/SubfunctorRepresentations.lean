import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Subfunctor Representations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

noncomputable section

/-! Converting between natural subfunctor representations and their concrete
factorization properties, without assuming representability of a target result. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {M Z : Over S}

theorem represented_subfunctor_mem (F : Subfunctor (yoneda.obj M)) (j : Z ⟶ M)
    (e : yoneda.obj Z ≅ F.toFunctor) (he : e.hom ≫ F.ι = yoneda.map j)
    (T : Over S) (x : T ⟶ M) : x ∈ F.obj (.op T) ↔ ∃ y : T ⟶ Z, y ≫ j = x := by
  have hval (y : T ⟶ Z) : (e.hom.app (.op T) y).val = y ≫ j := by
    change ((e.hom ≫ F.ι).app (.op T)) y = (yoneda.map j).app (.op T) y
    exact ConcreteCategory.congr_hom (NatTrans.congr_app he (.op T)) y
  constructor
  · intro hx
    let y := e.inv.app (.op T) ⟨x, hx⟩
    refine ⟨y, ?_⟩
    rw [← hval]
    exact congrArg Subtype.val ((e.app (.op T)).inv_hom_id_apply ⟨x, hx⟩)
  · rintro ⟨y, rfl⟩
    rw [← hval]
    exact (e.hom.app (.op T) y).property

theorem subfunctor_representation_of_lifts (F : Subfunctor (yoneda.obj M)) (j : Z ⟶ M) [Mono j]
    (h : ∀ (T : Over S) (x : T ⟶ M), x ∈ F.obj (.op T) ↔ ∃ y : T ⟶ Z, y ≫ j = x) :
    ∃ e : yoneda.obj Z ≅ F.toFunctor, e.hom ≫ F.ι = yoneda.map j := by
  let t : yoneda.obj Z ⟶ F.toFunctor := {
    app T := ↾fun y => ⟨y ≫ j, (h T.unop _).mpr ⟨y, rfl⟩⟩
    naturality := by
      intro T U a
      apply ConcreteCategory.hom_ext
      intro y
      exact Subtype.ext (Category.assoc _ _ _) }
  have : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app t).mpr
    intro T
    apply (isIso_iff_bijective _).mpr
    constructor
    · intro y z hyz
      exact (cancel_mono j).mp (congrArg Subtype.val hyz)
    · intro x
      obtain ⟨y, hy⟩ := (h T.unop x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨asIso t, rfl⟩

/-- A subfunctor is represented by a quasi-compact locally closed immersion.
This property is used for closure constructions on already proved loci. -/
def ImmersionRepresentable (F : Subfunctor (yoneda.obj M)) : Prop :=
  ∃ (Z : Over S) (j : Z ⟶ M), IsImmersion j.left ∧ QuasiCompact j.left ∧
    ∃ e : yoneda.obj Z ≅ F.toFunctor, e.hom ≫ F.ι = yoneda.map j

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations
