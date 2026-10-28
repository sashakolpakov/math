import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedScalar
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionFormChart
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointSupportedResidue

/-! # Finite Residue Choice -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Choose the genuine finite residue numerator inside the source of
the original paired frame and one native form chart. The residue formula
uses the original finite point data on the final ambient projective open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} {A : Geometry.AbelianH1Model K q jq}
  {n m : ℕ} {hm : ¬q ∣ m}
attribute [local instance] MvPolynomial.gradedAlgebra
variable
  {U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens}
  {hU : IsAffineOpen U}
  {D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU}
  (P : A.TruncatedPairedPointParameters n m hm U hU D)

variable
  (hgood : IntegralComparison.FiniteEtale.TraceBasis.Good (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U))
  (B : ℕ) (hB : A.truncatedTraceDimension n+2 ≤ B)

abbrev Geometry.AbelianH1Model.TruncatedPairedPointParameters.exists_finiteResidue := by
  let : IsFinite (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_finite n m hm
  let : AlgebraicGeometry.Etale (A.truncatedShiftOver n m hm).left :=
    A.truncatedShiftMap_etale n m hm
  have hchart := IntegralComparison.Intrinsic.SectionFormChart.exists_inside (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedShiftIdentitySection n m hm)
    P.sourceNeighborhood P.sourceNeighborhood_contains
  exact Exists.imp (fun j hj => by
    have hresidues := IntegralComparison.ProjectiveFinite.EtalePointSupportedResidue.exists_residue
        (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
        (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
        (A.truncatedShiftIdentitySection_over n m hm) B hB
        P.paired.ambient P.paired.affine P.finiteOriginal (P.final_good hgood)
        (P.sourceNeighborhood ⊓ OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens
          (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) j) hj
    exact Exists.imp (fun z hzall => by
      rcases hzall with ⟨hz, hzε, hzV, hzcontains, hresidue⟩
      have hzaffine : IsAffineOpen ((A.truncatedShiftModel n m hm).left.basicOpen z) :=
        ((P.final_good hgood).1.preimage (A.truncatedShiftOver n m hm).left).basicOpen z
      have hzbase : (A.truncatedShiftModel n m hm).left.basicOpen z ≤
          (A.truncatedShiftMap n m hm) ⁻¹ᵁ ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient) :=
        (A.truncatedShiftModel n m hm).left.basicOpen_le z
      have hzneighborhood : (A.truncatedShiftModel n m hm).left.basicOpen z ≤ P.sourceNeighborhood :=
        hzV.trans inf_le_left
      have hzchart : (A.truncatedShiftModel n m hm).left.basicOpen z ≤
          OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
            (A.truncatedShiftModel n m hm) j := hzV.trans inf_le_right
      exact And.intro hz <| And.intro hzε <| And.intro hzaffine <| And.intro hzbase <|
        And.intro hzneighborhood <| And.intro hzchart <|
        And.intro hzcontains hresidue) hresidues) hchart

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
