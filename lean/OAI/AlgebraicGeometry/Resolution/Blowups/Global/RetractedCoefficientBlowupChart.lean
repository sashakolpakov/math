import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyBlowupChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.GlobalCenterEquations
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RatioRetraction

/-! # Retracted Coefficient Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual retained native coefficient charts keep their algebraic line retractions after horizontal-center blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Polynomial

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale
  EtaleLine.ReferenceBase.Construction.etaleLineChart_originalScalarTower

def Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction.blowupChart
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData} {C : H.subscheme.IdealSheafData} {b : ℕ}
    {T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b} [IsNoetherianRing T.ring] [Algebra ℚ T.ring]
    (A : Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T)
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hHI : H ≤ I) (hp : J ≤ I ^ b)
    (hC : C ≤ (I.comap H.subschemeι) ^ b.factorial)
    (K : Ideal A.base) (hK : I.comap T.map = Affine.QuotientKernel.Construction.affineQuotientKernel (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := T.ring) K))
    (a : K) (j : Spec (.of (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := T.ring) K a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI) [Etale j]
    (hover : j ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI =
      Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K)
        (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := T.ring) K a))) ≫ T.map) :
    Σ T' : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1)
      (GlobalCoefficient.Transform.Construction.globalRetainedCoefficientTransform I H C hI b) b, Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T' := by
  let M := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := T.ring) K
  let d := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := T.ring) K a
  have hn : T.normal ∈ M := by
    rw [A.normal_eq]
    exact (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := T.ring) K).property
  have hd : T.derivative d.val = 0 := by
    change T.derivative (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap a.val) = 0
    rw [EtaleLine.NormalDerivation.Construction.etaleLineCoefficientMap_eq]
    exact A.derivative_coefficient a.val
  let T' := T.blowupChart I hI hHI hp hC M hK hn d hd j hover
  have hz : (⟨T.normal, hn⟩ : M) = Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K := Subtype.ext A.normal_eq
  let e : (T.ring ⧸ Ideal.span {algebraMap (Polynomial A.base) T.ring Polynomial.X}) ≃ₐ[A.base] A.base := by
    rw [← A.normal_eq]
    exact A.retraction
  refine ⟨T', {
    base := .of (Blowup.Charts.Construction.blowupChart K a)
    algebra := inferInstance
    action := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra (R := T.ring) K a
    lineAction := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra (R := T.ring) K a
    groundTower := EtaleLine.ReferenceBase.Construction.etaleLineChart_originalScalarTower ℂ K a
    lineTower := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower (R := T.ring) K a
    lineEtale := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale (R := T.ring) K a
    normal_eq := ?_
    derivative_eq := ?_
    retraction := ?_ }⟩
  · change ExceptionalIdeal.Construction.blowupChartRatio M d ⟨T.normal, hn⟩ =
      Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap (R := T.ring) K a Polynomial.X
    rw [hz]
    exact (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap_coordinate K a).symm
  · change Relative.DifferentialBlowup.Construction.blowupRelativeChartDerivation ℂ M d T.derivative =
      Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation ℂ (H := Blowup.Charts.Construction.blowupChart K a)
        (R := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := T.ring) K a)
    rw [A.derivative_eq]
    exact (EtaleLine.ReferenceBase.Construction.etaleLine_normalDerivation_original_base ℂ K a).symm
  · change (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := T.ring) K a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio M d ⟨T.normal, hn⟩}) ≃ₐ[
      Blowup.Charts.Construction.blowupChart K a] Blowup.Charts.Construction.blowupChart K a
    rw [hz]
    exact EtaleLine.RatioRetraction.Construction.etaleLineRatioFiberEquiv e K a

end

end OAI.AlgebraicGeometry.Resolution.Blowups
