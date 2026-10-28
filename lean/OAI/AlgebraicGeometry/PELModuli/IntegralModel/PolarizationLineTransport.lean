import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationFiberLine

/-! # Polarization Line Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineTransport.PolarizationAmpleness

noncomputable section

/-! The canonical polarization line bundle is preserved by actual
polarized-family isomorphisms. Positivity therefore makes it ample on
every given geometric polarized abelian variety, with no auxiliary choice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
  {A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))}

theorem polarizationLine_transport (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((PoincareClass.PoincareClasses.polarizationLine B.dual B.polarization.isogeny.hom).pullback e.abelian.hom.left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom) := by
  let d := lift A.polarization.isogeny.hom (𝟙 A.abelian.scheme)
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass d.left) e.poincare
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp] at h
  have hm : d ≫ (e.dual.hom ⊗ₘ e.abelian.hom) =
      e.abelian.hom ≫ lift B.polarization.isogeny.hom (𝟙 B.abelian.scheme) := by
    dsimp only [d]
    rw [lift_map, Category.id_comp, e.polarization, comp_lift, Category.comp_id]
  have hml : d.left ≫ (e.dual.hom ⊗ₘ e.abelian.hom).left =
      e.abelian.hom.left ≫ (lift B.polarization.isogeny.hom (𝟙 B.abelian.scheme)).left :=
    congrArg Over.Hom.left hm
  rw [hml, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp] at h
  exact h

variable [IsAlgClosed k]

/-- HilbertConstruction's original positivity suffices for ampleness of this fixed bundle. -/
theorem polarizationLine_isAmple (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    (PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom).IsAmple := by
  have hB := PolarizationFiberLine.PolarizationAmpleness.polarization_fiber_line_isAmple A.dual A.polarization.isogeny.hom
    (𝟙 (Spec (.of k))) (A.polarization.positive k (𝟙 (Spec (.of k))))
  let e := AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A
  have : IsIso e.abelian.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map e.abelian.hom))
  obtain ⟨h⟩ := Quotient.exact (polarizationLine_transport e)
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.isAmple_pullback_iff_of_isIso e.abelian.hom.left).mp (hB.of_iso h.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineTransport.PolarizationAmpleness
