import OAI.Analysis.HodgeTheory.Decomposition.SmoothGlobal
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Compact Inclusion -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CompactInclusion.Constructions

noncomputable section

/-! The genuine completed Hodge energy domain has compact inclusion into
the actual projective L² space. -/

open Set _root_.Metric

theorem mem_closure_bounded_image {A H : Type*} [NormedAddCommGroup H]
    (f : A → H) {u : H} (hu : u ∈ closure (range f)) {R : ℝ} (hR : ‖u‖ < R) :
    u ∈ closure (f '' {a | ‖f a‖ ≤ R}) := by
  rw [Metric.mem_closure_iff] at hu ⊢
  intro ε hε
  have hδ : 0 < min ε ((R - ‖u‖) / 2) := lt_min hε (half_pos (sub_pos.mpr hR))
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hu (min ε ((R - ‖u‖) / 2)) hδ
  refine ⟨f a, ⟨a, ?_, rfl⟩, ha.trans_le (min_le_left _ _)⟩
  have hnear := ha.trans_le (min_le_right _ _)
  have hn : ‖f a‖ ≤ ‖u‖ + dist u (f a) := by
    simpa only [sub_sub_cancel, dist_eq_norm] using norm_sub_le u (u - f a)
  change ‖f a‖ ≤ R
  linarith

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projectiveEnergyInclusion_isCompact : IsCompactOperator (EnergyDomain.Constructions.projectiveEnergyInclusion V n) := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact (EnergyDomain.Constructions.projectiveEnergyInclusion V n).toLinearMap
    (by norm_num : (0 : ℝ) < 1)).mpr
  let K := closure ((Form.Constructions.smoothToProjectiveL2 V (n + 1)) '' {a | ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ 2})
  refine ⟨K, SmoothGlobal.Constructions.projectiveSmooth_graph_ball_rellich V n 2 (by norm_num), ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hun : ‖u.val‖ < 2 := by
    have h : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    change ‖u.val‖ ≤ 1 at h
    linarith
  have hclosure := mem_closure_bounded_image (EnergyDomain.Constructions.projectiveGraphEmbedding V n) u.property hun
  have hmap : MapsTo (EnergyDomain.Constructions.projectiveGraphValue V n)
      ((EnergyDomain.Constructions.projectiveGraphEmbedding V n) '' {a | ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ 2})
      ((Form.Constructions.smoothToProjectiveL2 V (n + 1)) '' {a | ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ 2}) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  exact (EnergyDomain.Constructions.projectiveGraphValue V n).continuous.continuousAt.continuousWithinAt.mem_closure hclosure hmap

end

end OAI.Analysis.HodgeTheory.Decomposition.CompactInclusion.Constructions
