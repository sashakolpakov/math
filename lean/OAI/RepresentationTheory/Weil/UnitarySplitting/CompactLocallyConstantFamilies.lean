import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierUltra

/-! # Compact Locally Constant Families -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CompactLocallyConstantFamilies.Construction

noncomputable section

/-! Local constancy uniform on a compact set, with arbitrary topological
parameter spaces. -/

open _root_.MeasureTheory _root_.Topology Filter

theorem locallyConstant_uniform_on_compact
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    (k : P × X → Y) (hk : IsLocallyConstant k) (K : Set X) (hK : IsCompact K) (p : P) :
    ∀ᶠ t in 𝓝 p, ∀ x ∈ K, k (t, x) = k (p, x) := by
  have hk₀ : IsLocallyConstant (fun z : P × X => k (p, z.2)) :=
    hk.comp_continuous (continuous_const.prodMk continuous_snd)
  apply hK.eventually_forall_of_forall_eventually
  intro x _
  filter_upwards [hk.eventually_eq (p, x), hk₀.eventually_eq (p, x)] with z hz hz₀
  exact hz.trans hz₀.symm

theorem locallyConstant_family_of_local_compact_support
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X] [Zero Y]
    (k : P × X → Y) (hk : IsLocallyConstant k)
    (hsupport : ∀ p : P, ∃ K : Set X, IsCompact K ∧
      ∀ᶠ t in 𝓝 p, ∀ x : X, x ∉ K → k (t, x) = 0) :
    IsLocallyConstant (fun p : P => fun x : X => k (p, x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  obtain ⟨K, hK, hsupport⟩ := hsupport p
  have hp := hsupport.self_of_nhds
  filter_upwards [hsupport, locallyConstant_uniform_on_compact k hk K hK p] with t ht heq
  funext x
  by_cases hx : x ∈ K
  · exact heq x hx
  · rw [ht x hx, hp x hx]

theorem locallyConstant_parameter_integral
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (k : P × X → ℂ) (hk : IsLocallyConstant k)
    (K : Set X) (hK : IsCompact K) (hsupport : ∀ p x, x ∉ K → k (p, x) = 0) :
    IsLocallyConstant (fun p : P => ∫ x, k (p, x) ∂μ) :=
  (locallyConstant_family_of_local_compact_support k hk
    (fun _p => ⟨K, hK, Filter.Eventually.of_forall (fun t => hsupport t)⟩)).comp
      (fun f : X → ℂ => ∫ x, f x ∂μ)

theorem compact_pullback_family_local_support
    {P X : Type} [TopologicalSpace P] [NormedAddCommGroup X] [ProperSpace X]
    (L : P → X ≃ₜ X) (hL : Continuous (fun z : P × X => (L z.1).symm z.2))
    (K : Set X) (hK : IsCompact K) (p : P) :
    ∃ T : Set X, IsCompact T ∧ ∀ᶠ t in 𝓝 p, ∀ x : X, L t x ∈ K → x ∈ T := by
  obtain ⟨R, -, hR⟩ := (hK.image (L p).symm.continuous).isBounded.exists_pos_norm_le
  have he : ∀ᶠ t in 𝓝 p, ∀ y ∈ K, ‖(L t).symm y‖ < R + 1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro y hy
    have hbound : ‖(L p).symm y‖ < R + 1 := (hR _ ⟨y, hy, rfl⟩).trans_lt (lt_add_one R)
    exact hL.norm.continuousAt.eventually (gt_mem_nhds hbound)
  refine ⟨Metric.closedBall 0 (R + 1), isCompact_closedBall _ _, ?_⟩
  filter_upwards [he] with t ht x hx
  have hh := ht (L t x) hx
  rw [(L t).symm_apply_apply] at hh
  simpa only [Metric.mem_closedBall, dist_zero_right] using hh.le

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CompactLocallyConstantFamilies.Construction
