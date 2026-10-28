import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.Sections

noncomputable section

/-! Sections of a base-changed object classify morphisms from the base into the original object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] {S T X Y : C}
  {p : X ⟶ S} {q : Y ⟶ T} {g : Y ⟶ X} {f : T ⟶ S}

/-- The section-to-morphism equivalence supplied by a Cartesian square. -/
def cartesianSectionHomEquiv (h : IsPullback g q p f) :
    (Over.mk (𝟙 T) ⟶ Over.mk q) ≃ (Over.mk f ⟶ Over.mk p) where
  toFun u := Over.homMk (u.left ≫ g) (by
    change (u.left ≫ g) ≫ p = f
    have hu : u.left ≫ q = 𝟙 T := u.w
    rw [Category.assoc, h.w, ← Category.assoc, hu]
    exact Category.id_comp f)
  invFun u := Over.homMk (h.lift u.left (𝟙 T) (by
    have hu : u.left ≫ p = f := u.w
    exact hu.trans (Category.id_comp f).symm))
    (h.lift_snd _ _ _)
  left_inv u := by
    apply Over.OverMorphism.ext
    apply h.hom_ext
    · exact h.lift_fst _ _ _
    · exact (h.lift_snd _ _ _).trans u.w.symm
  right_inv u := Over.OverMorphism.ext (h.lift_fst _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.Sections
