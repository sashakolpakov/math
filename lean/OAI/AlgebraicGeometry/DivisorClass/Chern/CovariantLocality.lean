import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms

/-! # Covariant Locality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The original covariant derivatives do not enlarge support, by their proved restriction laws. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative_zero_off_closed
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) {K : Set M} (hK : IsClosed K)
    (ha : ∀ j (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)), x.val ∉ K → a.val j x = 0)
    (j : M) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) (hx : x.val ∉ K) :
    (h.covariantDerivative ⊤ a).val j x = 0 := by
  let U : Opens M := ⟨Kᶜ, hK.isOpen_compl⟩
  have hz : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (show U ≤ ⊤ from le_top) a = 0 := by
    apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
    intro k y
    exact ha k ⟨y.val, trivial, y.property.2⟩ y.property.1
  have hd : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (show U ≤ ⊤ from le_top) (h.covariantDerivative ⊤ a) = 0 := by
    rw [h.covariantDerivative_restrict ⊤ le_top, hz, map_zero]
  exact congrArg (fun b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1 => b.val j ⟨x.val, hx, x.property.2⟩) hd

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivativeOne_zero_off_closed
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) {K : Set M} (hK : IsClosed K)
    (ha : ∀ j (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)), x.val ∉ K → a.val j x = 0)
    (j : M) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) (hx : x.val ∉ K) :
    (h.covariantDerivativeOne ⊤ a).val j x = 0 := by
  let U : Opens M := ⟨Kᶜ, hK.isOpen_compl⟩
  have hz : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (show U ≤ ⊤ from le_top) a = 0 := by
    apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
    intro k y
    exact ha k ⟨y.val, trivial, y.property.2⟩ y.property.1
  have hd : HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict (show U ≤ ⊤ from le_top) (h.covariantDerivativeOne ⊤ a) = 0 := by
    rw [h.covariantDerivativeOne_restrict ⊤ le_top, hz, map_zero]
  exact congrArg (fun b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 2 => b.val j ⟨x.val, hx, x.property.2⟩) hd

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative_localized_zero
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f)
    (j : M) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) (hx : x.val ∉ tsupport f) :
    (h.covariantDerivative ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a)).val j x = 0 := by
  apply h.covariantDerivative_zero_off_closed _ (isClosed_tsupport f) _ j x hx
  intro k y hy
  rw [Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply, image_eq_zero_of_notMem_tsupport hy]
  ext v
  exact zero_mul _

end

/-! The original covariant derivatives do not enlarge support, by their proved restriction laws. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivativeOne_localized_zero
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f)
    (j : M) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) (hx : x.val ∉ tsupport f) :
    (h.covariantDerivativeOne ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a)).val j x = 0 := by
  apply h.covariantDerivativeOne_zero_off_closed _ (isClosed_tsupport f) _ j x hx
  intro k y hy
  rw [Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply, image_eq_zero_of_notMem_tsupport hy]
  ext v
  exact zero_mul _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
