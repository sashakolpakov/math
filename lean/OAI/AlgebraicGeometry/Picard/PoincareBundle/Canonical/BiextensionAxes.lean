import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.SecondDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.AxisDataOfOrdinary

/-! # Biextension Axes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BiextensionAxes

noncomputable section

/-!
# Canonical Poincare coordinate actions from quotient factorization and symmetry

No kernel-frame splitting or coordinate action is input. Both ordinary coordinate actions are
constructed from genuine line bundles on the two partial quotient products and their pullback maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B Z : Over S}
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (f : A ⟶ B) (μ : A ⟶ Z) (α : B ⟶ Z) (hα : f ≫ α = μ)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P μ).sheaf ≅
    (FirstBiextensionFactor.familyLine P μ).sheaf)

/-- Both canonical actions on the original Poincare-family line, with their separate cocycles proved. -/
def axisData : RectangularTransport.AxisData f f (Geometric.KernelLinearization.overModulePullbacks S) (FirstBiextensionFactor.familyLine P μ).sheaf :=
  AxisDataOfOrdinary.Ordinary.toAxisData f f (Geometric.KernelLinearization.overModulePullbacks S) (FirstBiextensionFactor.familyLine P μ).sheaf
    (FirstBiextensionDescent.sourceDatum P f μ α hα)
    (Symmetric.SecondDescent.sourceDatum f (FirstBiextensionFactor.familyLine P μ) (FirstBiextensionFactor.descendedLine P α)
      (FirstBiextensionFactor.pullbackIso P f μ α hα) symmetry)
    (Iso.refl _) (Iso.refl _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.BiextensionAxes
