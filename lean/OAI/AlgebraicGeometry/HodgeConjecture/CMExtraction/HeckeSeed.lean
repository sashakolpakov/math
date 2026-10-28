import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalThetaSeed

/-! # Hecke Seed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeSeed.Intrinsic

noncomputable section

/-! Construct the GeometricTheta source datum from the pre-prime model and test,
then prove all of its finite-coordinate hypotheses. -/

open scoped Classical _root_.Matrix
open _root_.CategoryTheory

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver))

def retainedThetaSeed :
    letI : TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) := ⊥
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E M.integral.base.extension.carrier s q (Fin s × Fin 3)
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) MpR MpF MpA := by
  letI : TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) := ⊥
  letI : TopologicalSpace
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j C).reference.b) := ⊥
  letI : DiscreteTopology
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j C).reference.b) := ⟨rfl⟩
  exact RationalThetaSeed.Intrinsic.rationalThetaSeed E (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j C)
    (HeckeModel.Intrinsic.retainedHeckeModel_geometry E P hP hμ v hv W R M j C) hμ v hv W R

theorem retainedThetaSeed_finiteCoordinates
    (hgood : PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q) :
    letI : TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) := ⊥
    (retainedThetaSeed E P hP hμ v hv W R M j C).HasFiniteCoordinates := by
  let : TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) := ⊥
  let : TopologicalSpace
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j C).reference.b) := ⊥
  let : DiscreteTopology
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j C).reference.b) := ⟨rfl⟩
  exact RationalThetaSeed.Intrinsic.rationalThetaSeed_finiteCoordinates E (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j C)
    (HeckeModel.Intrinsic.retainedHeckeModel_geometry E P hP hμ v hv W R M j C) hμ v hv W R hgood.frame_large

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeSeed.Intrinsic
