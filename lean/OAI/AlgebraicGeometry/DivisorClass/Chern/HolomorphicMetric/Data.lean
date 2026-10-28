import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.HermitianPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothCoverFunctions

/-! # Data -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data

noncomputable section

section

/-! Smooth positive Hermitian metrics on the original holomorphic line bundle. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

structure HolomorphicLineMetricData (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) where
  weight : ∀ i, Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i → ℝ
  smooth : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (weight i)
  positive : ∀ i x, 0 < weight i x
  transition : ∀ i j x (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)
      (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j),
    weight i ⟨x, hi⟩ =
      Complex.normSq ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩) * weight j ⟨x, hj⟩

variable {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

def HolomorphicLineMetricData.rescale (h : HolomorphicLineMetricData u) (f : M → ℝ)
    (hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : ∀ x, 0 < f x) : HolomorphicLineMetricData u where
  weight i x := f x.val * h.weight i x
  smooth i := (hs.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E)))).mul (h.smooth i)
  positive i x := mul_pos (hp x.val) (h.positive i x)
  transition i j x hi hj := by rw [h.transition i j x hi hj]; ring

def HolomorphicLineMetricData.localRatio (h k : HolomorphicLineMetricData u) (i : M)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : ℝ := h.weight i x / k.weight i x

theorem HolomorphicLineMetricData.localRatio_positive (h k : HolomorphicLineMetricData u)
    (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : 0 < h.localRatio k i x :=
  div_pos (h.positive i x) (k.positive i x)

theorem HolomorphicLineMetricData.localRatio_smooth (h k : HolomorphicLineMetricData u) (i : M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (h.localRatio k i) := by
  intro x
  exact (h.smooth i x).mul ((contDiffAt_inv ℝ (ne_of_gt (k.positive i x))).contMDiffAt.comp x (k.smooth i x))

theorem HolomorphicLineMetricData.localRatio_overlap (h k : HolomorphicLineMetricData u)
    (i j x : M) (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)
    (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j) :
    h.localRatio k i ⟨x, hi⟩ = h.localRatio k j ⟨x, hj⟩ := by
  unfold HolomorphicLineMetricData.localRatio
  rw [h.transition i j x hi hj, k.transition i j x hi hj]
  exact mul_div_mul_left _ _ (ne_of_gt (Complex.normSq_pos.mpr
    (Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j) ⟨x, hi, hj⟩)))

def HolomorphicLineMetricData.ratio (h k : HolomorphicLineMetricData u) : M → ℝ :=
  SmoothCoverFunctions.smoothCoverFunction (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u)
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain (h.localRatio k)

theorem HolomorphicLineMetricData.ratio_onOpen (h k : HolomorphicLineMetricData u)
    (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : h.ratio k x.val = h.localRatio k i x :=
  SmoothCoverFunctions.smoothCoverFunction_onOpen _ _ _ (h.localRatio_overlap k) i x

theorem HolomorphicLineMetricData.ratio_smooth (h k : HolomorphicLineMetricData u) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (h.ratio k) :=
  SmoothCoverFunctions.smoothCoverFunction_contMDiff _ _ _ (h.localRatio_overlap k) (h.localRatio_smooth k)

theorem HolomorphicLineMetricData.ratio_positive (h k : HolomorphicLineMetricData u) (x : M) :
    0 < h.ratio k x := SmoothCoverFunctions.smoothCoverFunction_pos _ _ _ (h.localRatio_positive k) x

theorem HolomorphicLineMetricData.ratio_weight (h k : HolomorphicLineMetricData u)
    (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    h.ratio k x.val * k.weight i x = h.weight i x := by
  rw [h.ratio_onOpen k i x]
  exact div_mul_cancel₀ _ (ne_of_gt (k.positive i x))

variable [FiniteDimensional ℝ E] [IsScalarTower ℝ ℂ E] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def holomorphicLineCanonicalMetric (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) : HolomorphicLineMetricData u where
  weight := HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u
  smooth := HolomorphicLine.HermitianPair.holomorphicLineMetricWeight_contMDiff u
  positive := HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_pos u
  transition := HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_transition u

end

/-! Exact change-of-metric ratios on the original holomorphic line bundle. -/

open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

theorem HolomorphicLineMetricData.ratio_self (h : HolomorphicLineMetricData u) (x : M) :
    h.ratio h x = 1 := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x
  rw [h.ratio_onOpen h x ⟨x, hx⟩]
  exact div_self (ne_of_gt (h.positive x ⟨x, hx⟩))

theorem HolomorphicLineMetricData.ratio_mul (h k l : HolomorphicLineMetricData u) (x : M) :
    h.ratio k x * k.ratio l x = h.ratio l x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x
  rw [h.ratio_onOpen k x ⟨x, hx⟩, k.ratio_onOpen l x ⟨x, hx⟩, h.ratio_onOpen l x ⟨x, hx⟩]
  exact div_mul_div_cancel₀ (ne_of_gt (k.positive x ⟨x, hx⟩))

theorem HolomorphicLineMetricData.ratio_inv (h k : HolomorphicLineMetricData u) (x : M) :
    (h.ratio k x)⁻¹ = k.ratio h x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x
  rw [h.ratio_onOpen k x ⟨x, hx⟩, k.ratio_onOpen h x ⟨x, hx⟩]
  exact inv_div _ _

theorem HolomorphicLineMetricData.ratio_rescale (h k : HolomorphicLineMetricData u)
    (f : M → ℝ) (hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hp : ∀ x, 0 < f x) (x : M) :
    (h.rescale f hs hp).ratio k x = f x * h.ratio k x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x
  rw [(h.rescale f hs hp).ratio_onOpen k x ⟨x, hx⟩, h.ratio_onOpen k x ⟨x, hx⟩]
  exact mul_div_assoc _ _ _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data
