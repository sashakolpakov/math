import OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineAmpleness
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedPositiveFormula

/-! # Diagonal Positivity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.DiagonalPositivity

noncomputable section

/-! The constructed quotient diagonal pulls back to an actual ample line, from the original polarization formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineAmpleness
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A B D : Over S} [GrpObj A] [GrpObj D] [A.left.IsSeparated]
  (P : Line.Bundles.LineBundle (D ⊗ A).left) (ell : A ⟶ D)
  (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P) (Dv : FiberwiseMultiplication.Multiplication (snd D A) (fst D A) P)
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple)
  (e0 : (L.pullback η[A].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
  (eL : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine P ell).sheaf (L.pullback (fst A A).left).sheaf)
    (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf)
  (n : ℕ) (hn : 0 < n) (f : A ⟶ B)
  (R : Line.Bundles.LineBundle (B ⊗ B).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ f).left).obj R.sheaf ≅ (FirstBiextensionFactor.familyLine P (ell ^ n)).sheaf)

include Dh Dv hL e0 eL hn e

/-- Actual quotient recovery and the original ample-line formula prove positivity of the pulled diagonal. -/
theorem pullback_isAmple : ((DiagonalLineClass.diagonalLine R (𝟙 B)).pullback f.left).IsAmple := by
  have hd : (DiagonalLineClass.diagonalLine P ell).IsAmple := DiagonalLineAmpleness.diagonalLine_isAmple P ell Dv L hL
    (NormalizedPositiveFormula.zero_class L e0) (NormalizedPositiveFormula.formula_class P ell L eL)
  have hnL := DiagonalLineAmpleness.diagonalLine_pow_isAmple P ell Dh hd n hn
  exact hnL.of_iso (DiagonalRecovery.pullbackIso f (ell ^ n) P R e).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.DiagonalPositivity
