import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeCodifferential
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeTests
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormIntegralPair

/-! # Degree Point Pairs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreePointPairs

noncomputable section

section

/-! Literal pointwise metric identities for the supported scalar adjoints. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance degreePointPairs_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (q : ℕ)

theorem holomorphicLineDegreeFrameAdjoint_zero (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) (j : V.analyticSpace)
    (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))
    (hx : x.val ∉ tsupport (FormPartition.holomorphicLineComplexPartition u i)) :
    (DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i a).val j x = 0 := by
  by_cases hi : x.val ∈ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i.val
  · rw [DegreeCodifferential.holomorphicLineDegreeFrameAdjoint_apply_mem V u q i a j x hi,
      DegreeCodifferential.holomorphicLineDegreeFrameAdjointForm_zero V u q i a ⟨x, hi⟩ hx]
    ext v
    change FormPartition.holomorphicLineFrameCutoff u i x *
      ((CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i.val j).val
        ⟨x, hi, x.property.2⟩ * 0) = 0
    ring
  · exact SupportedForms.holomorphicLineSupportedExtension_apply_zero u _ q
      (FormPartition.holomorphicLineFrameCutoff u i) (FormPartition.holomorphicLineFrameCutoff_smooth u i)
      (FormPartition.holomorphicLineFrameCutoff_support u i) _ j x
      (fun h => hi (FormPartition.holomorphicLineFrameCutoff_support u i h))

theorem holomorphicLineWeightedFrameExtension_pair (n : ℕ) (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (b d : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace)
    (hc : ∀ hx : x ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i),
      c x = d.val i.val ⟨x, trivial, FormPartition.holomorphicLineComplexPartition_support u i hx⟩) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i n b).val c.val x =
      FormPartition.holomorphicLineComplexPartition u i x * FormIntegralPair.holomorphicLineGlobalFormPair V u n b d x := by
  by_cases hx : x ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i)
  · have hi := FormPartition.holomorphicLineComplexPartition_support u i hx
    rw [Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
      HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension_apply u i n b ⟨x, hi⟩, hc hx,
      Projective.CovectorPair.projectiveTangentCovectorPair_smul_left, FormIntegralPair.holomorphicLineGlobalFormPair_apply,
      HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_inFrame V u n b d i.val ⟨x, trivial⟩ hi]
    simp only [map_mul, FormPartition.holomorphicLineComplexPartition, Complex.conj_ofReal]
    ring
  · have hb := HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension_zero u i n b x hx
    rw [Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_congr_at V n
      (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i n b).val c.val 0 c.val x hb rfl,
      Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_left, image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem holomorphicLineDegreeFrameAdjointPair_left (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V (q + 1) (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b).val
      (Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegree V q (DegreeTests.holomorphicLineDegreeFrameTest V u q i a.val)).val x =
        FormPartition.holomorphicLineComplexPartition u i x *
          FormIntegralPair.holomorphicLineGlobalFormPair V u (q + 1) b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val x :=
  holomorphicLineWeightedFrameExtension_pair V u (q + 1) i b (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ q a).val
    (Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegree V q (DegreeTests.holomorphicLineDegreeFrameTest V u q i a.val)) x
    (fun hx => DegreeTests.holomorphicLineDegreeFrameTest_dbar V u q i a
      ⟨x, FormPartition.holomorphicLineComplexPartition_support u i hx⟩ hx)

end

/-! The metric inverse and genuine frame cutoff identify the scalar and bundle adjoint pairings. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal
local instance degreeRightPair_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (q : ℕ)

theorem holomorphicLineDegreeFrameAdjoint_globalPair_zero (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) (x : V.analyticSpace)
    (hx : x ∉ tsupport (FormPartition.holomorphicLineComplexPartition u i)) :
    FormIntegralPair.holomorphicLineGlobalFormPair V u q (DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i b) a x = 0 := by
  rw [FormIntegralPair.holomorphicLineGlobalFormPair_apply]
  dsimp only [HolomorphicLine.FormPair.holomorphicLineSmoothFormPair]
  rw [holomorphicLineDegreeFrameAdjoint_zero V u q i b x _ hx, AdjointPointPairs.projectiveTangentCovectorPair_zero_left, mul_zero]

theorem holomorphicLineDegreeFrameAdjointPair_right (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ q) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (q + 1)) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V q
      (Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint V q (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b)).val
      (DegreeTests.holomorphicLineDegreeFrameTest V u q i a).val x =
        FormIntegralPair.holomorphicLineGlobalFormPair V u q (DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i b) a x := by
  by_cases hx : x ∈ tsupport (FormPartition.holomorphicLineComplexPartition u i)
  · have hi := FormPartition.holomorphicLineComplexPartition_support u i hx
    rw [Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
      DegreeTests.holomorphicLineDegreeFrameTest_on_partition_support V u q i a ⟨x, hi⟩ hx,
      FormIntegralPair.holomorphicLineGlobalFormPair_apply,
      HolomorphicLine.FormPair.holomorphicLineSmoothFormPair_inFrame V u q (DegreeCodifferential.holomorphicLineDegreeFrameAdjoint V u q i b) a i.val ⟨x, trivial⟩ hi,
      DegreeCodifferential.holomorphicLineDegreeFrameAdjoint_inFrame V u q i b ⟨x, hi⟩,
      DegreeCodifferential.holomorphicLineDegreeFrameAdjointForm_apply, Projective.CovectorPair.projectiveTangentCovectorPair_smul_left]
    simp only [map_inv₀, Complex.conj_ofReal]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_pos u i.val ⟨x, hi⟩))), one_mul]
  · have hb := Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint_zero_off_closed V q
      (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b) (isClosed_tsupport _)
      (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension_zero u i (q + 1) b) hx
    rw [Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_congr_at V q
      (Projective.DolbeaultAdjointDegrees.projectiveScalarDolbeaultDegreeAdjoint V q (HolomorphicMetric.FrameForms.holomorphicLineWeightedFrameExtension u i (q + 1) b)).val
      (DegreeTests.holomorphicLineDegreeFrameTest V u q i a).val 0 (DegreeTests.holomorphicLineDegreeFrameTest V u q i a).val x hb rfl,
      Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_left, holomorphicLineDegreeFrameAdjoint_globalPair_zero V u q i a b x hx]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreePointPairs
