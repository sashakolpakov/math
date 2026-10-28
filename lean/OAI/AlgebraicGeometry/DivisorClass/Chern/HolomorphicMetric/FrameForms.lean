import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormPartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.HermitianPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.HolomorphicProduct

/-! # Frame Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.FrameForms

noncomputable section

/-! Actual metric multiplication and weighted supported frame forms for integration by parts. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CompactSpace M] [T2Space M] (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)

def holomorphicLineSmoothMetricFunction (i : M) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :=
  ⟨fun x => (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i x : ℂ),
    Complex.ofRealCLM.contDiff.contMDiff.comp (HolomorphicLine.HermitianPair.holomorphicLineMetricWeight_contMDiff u i)⟩

def holomorphicLineSmoothInverseMetricFunction (i : M) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :=
  ⟨fun x => ((HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i x)⁻¹ : ℝ),
    Complex.ofRealCLM.contDiff.contMDiff.comp (by
      intro x
      exact (contDiffAt_inv ℝ (ne_of_gt (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_pos u i x))).contMDiffAt.comp x
        (HolomorphicLine.HermitianPair.holomorphicLineMetricWeight_contMDiff u i x))⟩

def holomorphicLineMetricFormMul (i : M) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n :=
  SmoothScalarForm.smoothScalarOpenFormMul (holomorphicLineSmoothMetricFunction u i)

def holomorphicLineInverseMetricFormMul (i : M) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n :=
  SmoothScalarForm.smoothScalarOpenFormMul (holomorphicLineSmoothInverseMetricFunction u i)

theorem holomorphicLineMetricFormMul_apply (i : M) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicLineMetricFormMul u i n a x = (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i x : ℂ) • a x :=
  SmoothScalarForm.smoothScalarOpenFormMul_apply _ _ _

theorem holomorphicLineInverseMetricFormMul_apply (i : M) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicLineInverseMetricFormMul u i n a x = ((HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i x : ℂ)⁻¹) • a x := by
  rw [holomorphicLineInverseMetricFormMul, SmoothScalarForm.smoothScalarOpenFormMul_apply]
  change (((HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i x)⁻¹ : ℝ) : ℂ) • a x = _
  rw [Complex.ofReal_inv]

theorem holomorphicLineInverseMetricFormMul_inverse (i : M) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n) :
    holomorphicLineInverseMetricFormMul u i n (holomorphicLineMetricFormMul u i n a) = a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [holomorphicLineInverseMetricFormMul_apply, holomorphicLineMetricFormMul_apply, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_pos u i x))), one_smul]

def holomorphicLineWeightedFrameCoordinates (i : M) (n : ℕ) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n :=
  (holomorphicLineMetricFormMul u i n).comp
    ((HolomorphicSmooth.Frames.holomorphicLineSmoothFrameEquiv u i le_rfl n).toLinearMap.comp (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top))

theorem holomorphicLineWeightedFrameCoordinates_apply (i : M) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicLineWeightedFrameCoordinates u i n a x =
      (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i x : ℂ) • a.val i ⟨x, trivial, x.property⟩ :=
  holomorphicLineMetricFormMul_apply u i n _ x

def holomorphicLineWeightedFrameExtension (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) (n : ℕ) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n :=
  (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)
    (Holomorphic.FormPartition.holomorphicLineComplexPartition_smooth u i).contMDiffOn
    (Holomorphic.FormPartition.holomorphicLineComplexPartition_support u i)).comp (holomorphicLineWeightedFrameCoordinates u i.val n)

theorem holomorphicLineWeightedFrameExtension_apply (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i.val) :
    holomorphicLineWeightedFrameExtension u i n a x =
      (Holomorphic.FormPartition.holomorphicLineComplexPartition u i x * (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i.val x : ℂ)) •
        a.val i.val ⟨x, trivial, x.property⟩ := by
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)
    (Holomorphic.FormPartition.holomorphicLineComplexPartition_smooth u i).contMDiffOn (Holomorphic.FormPartition.holomorphicLineComplexPartition_support u i)
    (holomorphicLineWeightedFrameCoordinates u i.val n a) x = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension_apply_mem,
    holomorphicLineWeightedFrameCoordinates_apply, smul_smul]

theorem holomorphicLineWeightedFrameExtension_zero (i : HolomorphicLine.MetricWeight.holomorphicLineFiniteCover u) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : M) (hx : x ∉ tsupport (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)) :
    holomorphicLineWeightedFrameExtension u i n a x = 0 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension_eq_zero_of_notMem_tsupport (Holomorphic.FormPartition.holomorphicLineComplexPartition u i)
    (Holomorphic.FormPartition.holomorphicLineComplexPartition_smooth u i).contMDiffOn (Holomorphic.FormPartition.holomorphicLineComplexPartition_support u i)
    (holomorphicLineWeightedFrameCoordinates u i.val n a) hx

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.FrameForms
