import OAI.RepresentationTheory.Theta.Geometric.PresentedDiagonalLine
import OAI.RepresentationTheory.Theta.Geometric.DiagonalBiextensionForm

/-! # Presented Diagonal Form -/

namespace OAI.RepresentationTheory.Theta.Geometric.PresentedDiagonalForm

noncomputable section

/-! The actual total-family polarization diagonal has exactly twice
the native Chern form of each genuine geometric polarization witness. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} {S : Scheme.{0}} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) (s : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback s))

theorem presentedRelativeDiagonalForm
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.pullback s).scheme.left)
    (e : ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s).tensor
      (L.pullback (fst (A.pullback s).scheme (A.pullback s).scheme).left) |>.tensor
        (L.pullback (snd (A.pullback s).scheme (A.pullback s).scheme).left)).sheaf ≅
          (L.pullback (MonObj.mul (X := (A.pullback s).scheme)).left).sheaf)
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P.variety) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm P.variety (PresentedDiagonalLine.presentedRelativeDiagonalLine D p s P) v w =
      2 * AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm P.variety (L.pullback P.comparison.inv.left) v w := by
  have et := AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionFormulaTransport.biextensionFormula_transport P.variety.toOver (A.pullback s).scheme
    P.comparison.inv L (AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s) e
  have h := DiagonalBiextensionForm.diagonalBiextension_chernForm P.variety (L.pullback P.comparison.inv.left)
    (PresentedDiagonalLine.presentedRelativeBiextension D p s P) et v w
  have hi := congrArg (fun b => b v w)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm_iso P.variety _ _ (PresentedDiagonalLine.presentedRelativeDiagonalIso D p s P))
  exact hi.symm.trans h

end

end OAI.RepresentationTheory.Theta.Geometric.PresentedDiagonalForm
