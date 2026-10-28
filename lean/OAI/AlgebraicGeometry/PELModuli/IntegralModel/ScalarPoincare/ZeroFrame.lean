import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ScalarIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.Line

/-! # Zero Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Scalar change retains the original actual abelian-zero frame of
the Poincare bundle, using the literal commutative pullback square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) {S : Scheme.{0}} (b : S ⟶ Spec (.of R))

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareZeroFrame :
    ((U.scalarPoincareLine b).pullback ((Over.pullback b).map U.prescribedPoincareZero).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj U.prescribedDualTotalSpace).left :=
  LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left U.prescribedPoincareFrame
    (pullback.fst U.prescribedPoincareSpace.hom b) ((Over.pullback b).map U.prescribedPoincareZero).left
    (pullback.fst U.prescribedDualTotalSpace.hom b)
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality U.prescribedPoincareZero))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
