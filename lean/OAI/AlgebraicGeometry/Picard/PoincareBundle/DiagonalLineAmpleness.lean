import OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor

/-! # Diagonal Line Ampleness -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineAmpleness

noncomputable section

/-! Positivity of the actual Poincare diagonal and of its positive scalar multiples. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.LineClasses OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness

variable {S : Scheme.{u}} {A D : Over S} [GrpObj A]
  (P : Line.Bundles.LineBundle (D ⊗ A).left) (ell : A ⟶ D)
  (Dv : FiberwiseMultiplication.Multiplication (snd D A) (fst D A) P)

include Dv in
/-- The normalized ample inducing line makes the actual Poincare diagonal ample. -/
theorem diagonalLine_isAmple [A.left.IsSeparated] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple)
    (hzero : Homomorphisms.SchemePullback.Construction.schemePicardPullback (1 : A ⟶ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (hFormula : DiagonalLineClass.biextensionClass P ell *
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    (DiagonalLineClass.diagonalLine P ell).IsAmple := by
  have : IsIso (GrpObj.inv (X := A)).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (GrpObj.inv (X := A))))
  obtain ⟨e⟩ := Quotient.exact (DiagonalLineClass.diagonalLine_symmetrization P ell Dv L hzero hFormula)
  exact (PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness.tensor_isAmple hL (hL.pullback_of_isIso (GrpObj.inv (X := A)).left)).of_iso e.symm

variable [GrpObj D] (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P)

include Dh

omit [GrpObj A] in
/-- Scalar multiplication tensors the actual diagonal line class by the same positive power. -/
theorem diagonalLine_pow_class (n : ℕ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DiagonalLineClass.diagonalLine P (ell ^ n)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DiagonalLineClass.diagonalLine P ell) ^ n :=
  Poincare.LineClasses.pairClass_pow_left P Dh ell (𝟙 A) n

omit [GrpObj A] in
/-- Positive scalar multiplication preserves ampleness of the Poincare diagonal. -/
theorem diagonalLine_pow_isAmple (hL : (DiagonalLineClass.diagonalLine P ell).IsAmple) (n : ℕ) (hn : 0 < n) :
    (DiagonalLineClass.diagonalLine P (ell ^ n)).IsAmple := by
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DiagonalLineClass.diagonalLine P (ell ^ n)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((DiagonalLineClass.diagonalLine P ell).tensorPower n) :=
    (diagonalLine_pow_class P ell Dh n).trans (PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness.tensorPower_class (DiagonalLineClass.diagonalLine P ell) n).symm
  obtain ⟨e⟩ := Quotient.exact hc
  exact (hL.tensorPower n hn).of_iso e.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineAmpleness
