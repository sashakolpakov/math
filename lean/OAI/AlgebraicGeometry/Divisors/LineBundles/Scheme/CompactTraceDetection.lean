import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.FundamentalTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd

/-! # Compact Trace Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.CompactTraceDetection.BundleCycles

noncomputable section

/-! Compact tests outside a sufficiently small actual algebraic closed
set detect ordinary cohomology on a general smooth complex scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

local instance : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : QuasiCompact X.hom := inferInstance
  exact ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X

theorem schemeCohomology_zero_of_compactTrace_outside_closed
    (F : Closeds X.left) (c : ℕ)
    (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (p n : ℕ) (hn : p + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (hp : p + 1 < 2 * c) (a : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X p)
    (ha : ∀ (L : Compacts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)),
      (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X F.compl →
      ∀ b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))ᶜ n,
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
        (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p n hn a
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) L n b) = 0) :
    a = 0 := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let U := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X F.compl
  let r := AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) T (U : Set T) p
  let : IsIso r := CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions.closedComplement_restriction_isIso X F c hc p hp
  have hr : r a = 0 := by
    apply (AlgebraicTopology.Duality.Poincare.CompactSupportAnd.cohomology_eq_iff_compactSupportStage_evaluation_eq
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) (M := U) p n hn (r a) 0).mpr
    intro K b
    let e := AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenStageIso (X := T) U K n
    have h := CycleClass.Thom.Open.CompactPairing.Constructions.evaluation_openStage
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) U K p n hn a (e.inv b)
    have hz := ha (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := T) U K) (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset (X := T) U K) (e.inv b)
    change _ = AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      (M := U) p n hn (r a)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K n (e.hom (e.inv b))) at h
    rw [Iso.inv_hom_id_apply] at h
    exact (h.symm.trans hz).trans (by simp only [map_zero, LinearMap.zero_apply])
  have he := congrArg (inv r) hr
  exact (Iso.hom_inv_id_apply (asIso r) a).symm.trans (he.trans (map_zero _))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.CompactTraceDetection.BundleCycles
