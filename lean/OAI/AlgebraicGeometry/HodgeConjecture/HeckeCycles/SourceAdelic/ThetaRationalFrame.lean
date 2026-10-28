import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PhaseMatrixReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GlobalFrames

/-! # Theta Rational Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM

noncomputable section

/-! The rational frame supplied by the full AdelicTheta conclusion, expressed in
the original source index and polarization. Compatibility is proved from
AdelicTheta's coordinate conclusion and the actual source trace pairing. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

abbrev Data := RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (Source.QuadraticConjugation.CM.Field.RealField E)
  (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
  (Source.QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
  (Source.BallArithmetic.CM.data E L)

def index : GeometricSource.CM.Positions E places ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) where
  toFun i := (i.1, i.2, 0)
  invFun j := (j.1, j.2.1)
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))

def native (T : Data E L) : GeometricSource.CM.Vec E ≃ₗ[ℚ]
    ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) ⊕
      RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L)) → ℚ) :=
  ((Source.TensorAction.CM.tensorEquiv E
    (OppositeCoordinates.CM.coordinates E L.coordinates)).restrictScalars ℚ).trans
      (((Source.GlobalFrames.CM.frames E
        (OppositeCoordinates.CM.coordinates E L.coordinates)).rational.coordinates.restrictScalars ℚ).trans
          T.rationalPhase)

def frame (T : Data E L) : GeometricSource.CM.Vec E ≃ₗ[ℚ]
    ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :=
  (native E L T).trans (PhaseMatrixReindex.CM.swap (index E L))

variable (T : Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))

include hT in
theorem native_pairing (x y : GeometricSource.CM.Vec E) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (native E L T x) (native E L T y) =
      Algebra.trace ℚ E (L.coordinates.delta * -L.coordinates.a * GeometricSource.CM.hermitian E B.b x y) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (T.rationalPhase _) (T.rationalPhase _) = _
  rw [hT.2.2.1]
  change Algebra.trace ℚ (Source.QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1
    ((Source.GlobalFrames.CM.frames E
      (OppositeCoordinates.CM.coordinates E L.coordinates)).rational.coordinates
        (Source.TensorPairing.CM.tensorVector E
          (OppositeCoordinates.CM.coordinates E L.coordinates) x))
    ((Source.GlobalFrames.CM.frames E
      (OppositeCoordinates.CM.coordinates E L.coordinates)).rational.coordinates
        (Source.TensorPairing.CM.tensorVector E
          (OppositeCoordinates.CM.coordinates E L.coordinates) y))) = _
  rw [(Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)).rational.preserves]
  rw [Source.TensorPairing.CM.source_pairing]
  rfl

include hT in
theorem frame_pairing (x y : GeometricSource.CM.Vec E) :
    Source.ComplexAction.CM.Symplectic.pairing (frame E L T x) (frame E L T y) =
      Algebra.trace ℚ E (L.coordinates.delta * L.coordinates.a * GeometricSource.CM.hermitian E B.b x y) := by
  change Source.ComplexAction.CM.Symplectic.pairing
    (PhaseMatrixReindex.CM.swap (index E L) (native E L T x))
    (PhaseMatrixReindex.CM.swap (index E L) (native E L T y)) = _
  rw [PhaseMatrixReindex.CM.swap_pairing, native_pairing E L T hT]
  have he : L.coordinates.delta * -L.coordinates.a * GeometricSource.CM.hermitian E B.b x y =
      -(L.coordinates.delta * L.coordinates.a * GeometricSource.CM.hermitian E B.b x y) := by ring
  rw [he, map_neg, neg_neg]

def changeOfFrame : ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) ≃ₗ[ℚ]
    ((GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :=
  (Source.ComplexAction.CM.Symplectic.frame E L.coordinates).symm.trans (frame E L T)

include hT in
theorem change_pairing (x y : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℚ) :
    Source.ComplexAction.CM.Symplectic.pairing
      (changeOfFrame E L T x) (changeOfFrame E L T y) =
      Source.ComplexAction.CM.Symplectic.pairing x y := by
  change Source.ComplexAction.CM.Symplectic.pairing
    (frame E L T ((Source.ComplexAction.CM.Symplectic.frame E L.coordinates).symm x))
    (frame E L T ((Source.ComplexAction.CM.Symplectic.frame E L.coordinates).symm y)) = _
  rw [frame_pairing E L T hT, ← Source.ComplexAction.CM.Symplectic.frame_pairing,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def matrix : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) ℚ :=
  ⟨LinearMap.toMatrix' (changeOfFrame E L T).toLinearMap,
    Source.ComplexAction.CM.Symplectic.matrix_symplectic _ (by
      intro x y
      simpa only [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using
        change_pairing E L T hT x y)⟩

theorem matrix_source (x : GeometricSource.CM.Vec E) :
    (matrix E L T hT).val *ᵥ Source.ComplexAction.CM.Symplectic.frame E L.coordinates x =
      frame E L T x := by
  change (LinearMap.toMatrix' (changeOfFrame E L T).toLinearMap) *ᵥ _ = _
  rw [LinearMap.toMatrix'_mulVec]
  exact congrArg (frame E L T)
    ((Source.ComplexAction.CM.Symplectic.frame E L.coordinates).symm_apply_apply x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM
