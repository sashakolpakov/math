import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValueData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValueData

/-! # Point Value Trace Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointValueTraceCoordinates

noncomputable section

/-! The unweighted global values in the local fraction formulas are the
original native point values, with their original inverse Serre maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq) (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ordinary_trace :
    TruncatedModel.SmoothPointValueData.tracePoint (g := A.dimension) q (ZMod q) n
      (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
      (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
      (A.truncatedTraceDimension n+2) le_rfl = A.truncatedSerrePointClass n := rfl

def ordinaryGlobalMap
    (x : Smooth.ProjectiveFormTrace.cohomology (A.truncatedModel n).scheme
      (A.truncatedTraceMorphism n) A.dimension) :
    A.NativeBoundedCrystallineCohomology n (A.dimension+A.dimension) :=
  (TruncatedModel.AdditiveGlobal.globalHomologyIso q (ZMod q) n (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedPointValueResolution n)
    (A.dimension+A.dimension)).hom
      (TruncatedModel.ModelTopCoverComparison.globalInput q (ZMod q) n (A.truncatedModel n).scheme
        A.specialFiber.scheme (A.truncatedReduction n) (A.truncatedReductionSquare n)
        (A.truncatedPointValueResolution n) A.dimension
        (Intrinsic.TopFormTrace.cover (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))
        (Intrinsic.TopFormTrace.cover_top (A.truncatedModel n).scheme (A.truncatedTraceMorphism n))
        (ULift.up.{2,1} (ULift.up.{1,0}
          ((Intrinsic.TopFormTrace.serreIso (A.truncatedModel n).scheme
            (A.truncatedTraceMorphism n) A.dimension).inv x))))

def ordinaryValue : A.NativeBoundedCrystallineCohomology n (A.dimension+A.dimension) :=
  ordinaryGlobalMap A n
    (TruncatedModel.SmoothPointValueData.tracePoint (g := A.dimension) q (ZMod q) n
      (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
      (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
      (A.truncatedTraceDimension n+2) le_rfl)

section OrdinaryIdentity
attribute [local irreducible] HomologicalComplex.homology Intrinsic.TopFormTrace.serreIso

theorem ordinary_original : ordinaryGlobalMap A n (A.truncatedSerrePointClass n) =
    A.truncatedOrdinaryPointValue n := by
  simp only [ordinaryGlobalMap, GeometricComparison.Geometry.AbelianH1Model.truncatedOrdinaryPointValue, GeometricComparison.Geometry.AbelianH1Model.truncatedTracePointClass]

theorem ordinary : ordinaryValue A n = A.truncatedOrdinaryPointValue n :=
  (congrArg (ordinaryGlobalMap A n) (ordinary_trace A n)).trans (ordinary_original A n)

end OrdinaryIdentity

variable (m : ℕ) (hm : ¬q ∣ m)
local instance finiteMap : IsFinite (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_finite n m hm
local instance etaleMap : Etale (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_etale n m hm

theorem finite_trace :
    TruncatedModel.FinitePointValueData.tracePoint (g := A.dimension) q (ZMod q) n
      (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
      (A.truncatedShiftIdentitySection_over n m hm) (A.truncatedTraceDimension n+2) le_rfl =
    A.truncatedShiftSerrePointClass n m hm := rfl

def finiteGlobalMap
    (x : FiniteEtale.ProperTraceBase.cohomology (A.truncatedModel n).scheme
      (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedTraceMorphism n) A.dimension) :
    A.NativeBoundedCrystallineCohomology n (A.dimension+A.dimension) :=
  (TruncatedModel.AdditiveGlobal.globalHomologyIso q (ZMod q) n (A.truncatedShiftModel n m hm)
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedPointValueResolution n)
    (A.dimension+A.dimension)).hom
      (TruncatedModel.ModelTopCoverComparison.globalInput q (ZMod q) n (A.truncatedShiftModel n m hm)
        A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedShiftModel_square n m hm)
        (A.truncatedPointValueResolution n) A.dimension
        (A.truncatedFinitePointCover n m hm) (A.truncatedFinitePointCover_top n m hm)
        (ULift.up.{2,1} (ULift.up.{1,0}
          ((Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso (A.truncatedModel n).scheme
            (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
            (A.truncatedTraceMorphism n) A.dimension).inv x))))

def finiteValue : A.NativeBoundedCrystallineCohomology n (A.dimension+A.dimension) :=
  finiteGlobalMap A n m hm
    (TruncatedModel.FinitePointValueData.tracePoint (g := A.dimension) q (ZMod q) n
      (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
      (A.truncatedShiftIdentitySection_over n m hm) (A.truncatedTraceDimension n+2) le_rfl)

attribute [local irreducible] HomologicalComplex.homology Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso

theorem finite_original : finiteGlobalMap A n m hm (A.truncatedShiftSerrePointClass n m hm) =
    A.truncatedFinitePointValue n m hm := by
  simp only [finiteGlobalMap, GeometricComparison.Geometry.AbelianH1Model.truncatedFinitePointValue, GeometricComparison.Geometry.AbelianH1Model.truncatedFiniteTracePointClass]

theorem finite : finiteValue A n m hm = A.truncatedFinitePointValue n m hm :=
  (congrArg (finiteGlobalMap A n m hm) (finite_trace A n m hm)).trans (finite_original A n m hm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointValueTraceCoordinates
