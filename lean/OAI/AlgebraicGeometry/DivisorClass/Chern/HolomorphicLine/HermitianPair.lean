import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.MetricWeight
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! # Hermitian Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.HermitianPair

noncomputable section

section

/-! The positive local metric coefficients are genuinely smooth, including across frame boundaries. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem complexNormSq_contDiff : ContDiff ℝ ∞ Complex.normSq := by
  change ContDiff ℝ ∞ (fun z : ℂ => z.re * z.re + z.im * z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsScalarTower ℝ ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)

theorem holomorphicLineMetricSummand_contMDiff (i : M) (j : MetricWeight.holomorphicLineFiniteCover u) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (MetricWeight.holomorphicLineMetricSummand u i j) := by
  intro x
  by_cases hxj : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j.val
  · let g := (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j.val).val
    have hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (Holomorphic.OpenExtension.holomorphicOpenExtend g) x.val :=
      Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex ((Holomorphic.OpenExtension.holomorphicOpenExtend_contMDiffOn g).contMDiffAt
        ((Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j.val).isOpen.mem_nhds
          ⟨x.property, hxj⟩))
    have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (fun y => MetricWeight.holomorphicLineSmoothPartition u j y * Complex.normSq (Holomorphic.OpenExtension.holomorphicOpenExtend g y)) x.val :=
      (MetricWeight.holomorphicLineSmoothPartition u j).contMDiff.contMDiffAt.mul
        (complexNormSq_contDiff.contMDiff.contMDiffAt.comp x.val hg)
    apply (hf.comp x (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).contMDiffAt).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j.val).isOpen.mem_nhds hxj)] with y hy
    change y.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j.val at hy
    change MetricWeight.holomorphicLineMetricSummand u i j y =
      MetricWeight.holomorphicLineSmoothPartition u j y.val * Complex.normSq (Holomorphic.OpenExtension.holomorphicOpenExtend g y.val)
    erw [MetricWeight.holomorphicLineMetricSummand, dite_eq_left hy,
      Holomorphic.OpenExtension.holomorphicOpenExtend_apply g y.val ⟨y.property, hy⟩]
  · have hsupport : x.val ∉ tsupport (MetricWeight.holomorphicLineSmoothPartition u j) :=
      fun h => hxj (MetricWeight.holomorphicLineSmoothPartition_support u j h)
    have he := (notMem_tsupport_iff_eventuallyEq.mp hsupport).comp_tendsto
      (continuous_subtype_val.continuousAt : Tendsto (Subtype.val : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i → M)
        (𝓝 x) (𝓝 x.val))
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change MetricWeight.holomorphicLineSmoothPartition u j y.val = 0 at hy
    unfold MetricWeight.holomorphicLineMetricSummand
    split_ifs
    · rw [hy, zero_mul]
    · rfl

theorem holomorphicLineMetricWeight_contMDiff (i : M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (MetricWeight.holomorphicLineMetricWeight u i) := by
  apply ContMDiff.sum
  intro j _
  exact holomorphicLineMetricSummand_contMDiff u i j

end

/-! The local positive Hermitian pairings agree under the original bundle coordinate changes. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (u : Holomorphic.Connecting.holomorphicUnitCohomology E M)

def holomorphicLineHermitianPair (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (v w : ℂ) : ℂ :=
  (MetricWeight.holomorphicLineMetricWeight u i x : ℂ) * conj v * w

theorem holomorphicLineHermitianPair_self (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (v : ℂ) :
    holomorphicLineHermitianPair u i x v v =
      (MetricWeight.holomorphicLineMetricWeight u i x * Complex.normSq v : ℝ) := by
  simp only [holomorphicLineHermitianPair, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, mul_assoc]

theorem holomorphicLineHermitianPair_pos (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)
    (v : ℂ) (hv : v ≠ 0) : 0 < (holomorphicLineHermitianPair u i x v v).re := by
  rw [holomorphicLineHermitianPair_self]
  exact mul_pos (MetricWeight.holomorphicLineMetricWeight_pos u i x) (Complex.normSq_pos.mpr hv)

theorem holomorphicLineHermitianPair_transition (i j x : M)
    (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)
    (v w : ℂ) :
    holomorphicLineHermitianPair u j ⟨x, hj⟩
      (Bundle.holomorphicCohomologyCoordChange E M u i j x v) (Bundle.holomorphicCohomologyCoordChange E M u i j x w) =
        holomorphicLineHermitianPair u i ⟨x, hi⟩ v w := by
  rw [Bundle.holomorphicCohomologyCoordChange_apply E M u i j x hi hj,
    Bundle.holomorphicCohomologyCoordChange_apply E M u i j x hi hj]
  unfold holomorphicLineHermitianPair
  rw [MetricWeight.holomorphicLineMetricWeight_transition u i j x hi hj, Complex.ofReal_mul,
    Complex.normSq_eq_conj_mul_self, map_mul]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.HermitianPair
