import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicIdentity

/-! # Regular Holomorphic Line -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RegularHolomorphicLine.AnalyticLocal

noncomputable section

/-! A nonzero holomorphic germ is nonzero on some complex line through
its center. The proof uses the one-variable identity principle. -/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]

theorem exists_regular_holomorphic_line {F : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {x : E} (hx : x ∈ U)
    (hn : ¬∀ᶠ y in 𝓝 x, F y = 0) :
    ∃ v : E, v ≠ 0 ∧ ¬∀ᶠ z in 𝓝 (0 : ℂ), F (x + z • v) = 0 := by
  by_cases hfx : F x = 0
  · obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    obtain ⟨y, hyF, hy⟩ := ((not_eventually.mp hn).and_eventually (ball_mem_nhds x hR)).exists
    have hyx : y ≠ x := fun he => hyF (he ▸ hfx)
    let v := y - x
    have hv : v ≠ 0 := sub_ne_zero.mpr hyx
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hvr : ‖v‖ < R := mem_ball_iff_norm.mp hy
    let r := R / ‖v‖
    have h1r : 1 < r := (lt_div_iff₀ hvpos).mpr (by simpa only [one_mul] using hvr)
    let line : ℂ → E := fun z => x + z • v
    have hline : Differentiable ℂ line :=
      (differentiable_const x).add (differentiable_id.smul_const v)
    have hmaps : MapsTo line (ball (0 : ℂ) r) U := by
      intro z hz
      apply hball
      rw [mem_ball_iff_norm]
      change ‖x + z • v - x‖ < R
      rw [add_sub_cancel_left, norm_smul]
      calc
        ‖z‖ * ‖v‖ < r * ‖v‖ := mul_lt_mul_of_pos_right (by simpa using hz) hvpos
        _ = R := div_mul_cancel₀ _ hvpos.ne'
    refine ⟨v, hv, ?_⟩
    intro hz
    have he := ComplexGroups.HolomorphicAlgebraicity.HolomorphicIdentity.Constructions.Identity.eqOn_zero_ball_of_eventually_zero
      (hF.comp hline.differentiableOn hmaps) hz
    have hzero := he (show (1 : ℂ) ∈ ball 0 r by simpa using h1r)
    apply hyF
    simpa only [Function.comp_def, line, v, one_smul, ← add_sub_assoc,
      add_sub_cancel_left, Pi.zero_apply] using hzero
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine ⟨v, hv, ?_⟩
    intro hz
    have hzero := hz.self_of_nhds
    exact hfx (by simpa only [zero_smul, add_zero] using hzero)

end

end OAI.AlgebraicGeometry.Comparison.Betti.RegularHolomorphicLine.AnalyticLocal
