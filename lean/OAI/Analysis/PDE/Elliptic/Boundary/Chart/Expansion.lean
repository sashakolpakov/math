import OAI.Analysis.PDE.Elliptic.Boundary.InversePullback
import OAI.Analysis.PDE.Elliptic.Boundary.SlopeFromGradient
import OAI.Analysis.PDE.Elliptic.Boundary.LocalExpansion

/-! Boundary Hölder estimate transported through an actual local chart.
All constants are uniform in the chart and solution subject to the displayed
first/second derivative and ellipticity bounds. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

theorem boundary_chart_first_order_expansion
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∀ V : ℝ, 0 ≤ V →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (P F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ ι → ℝ),
      (∀ z ∈ closedHalfBall v, ContDiffAt ℝ 2 F z) →
      (∀ z ∈ closedHalfBall v, ContDiffAt ℝ 2 u (F z)) →
      (∀ z ∈ closedHalfBall v, DifferentiableAt ℝ P (F z)) →
      (∀ z ∈ closedHalfBall v, (fun y => P (F y)) =ᶠ[𝓝 z] id) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ F z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 F z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖pullbackEllipticOperator (fderiv ℝ P (F z)) (A (F z))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ∀ w,
        lam * ‖w‖ ^ 2 ≤ inner ℝ w (pullbackEllipticOperator (fderiv ℝ P (F z)) (A (F z)) w)) →
      (∀ z ∈ closedHalfBall v, ∀ w,
        inner ℝ w (pullbackEllipticOperator (fderiv ℝ P (F z)) (A (F z)) w) ≤ L * ‖w‖ ^ 2) →
      (∀ z ∈ openHalfBall v, |ellipticTrace A u (F z)| ≤ V) →
      (∀ z, ‖z‖ ≤ 1 → inner ℝ v z = 0 → u (F z) = 0) →
      ∀ z, ‖z‖ ≤ 1 / 4 → inner ℝ v z = 0 →
      ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, ‖x - z‖ ≤ r / 2 → 0 ≤ inner ℝ v x →
        |u (F x) - (fderiv ℝ u (F z) (fderiv ℝ F z v)) * inner ℝ v x| ≤
          C * r ^ α * inner ℝ v x := by
  obtain ⟨α, hα, hα1, hholder⟩ := boundary_centered_expansion_local (ι := ι) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro V hV
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  let K := (V + d * V ^ 3) / (2 * lam * d)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨C, hC, hholder⟩ := hholder (-(V * V)) (V * V) K (by nlinarith) hK
  refine ⟨C, hC, ?_⟩
  intro v hv A P F u hF hu hP hinv hDu hDF hDDF hB hlo hhi hLu hzero z hz hvz r hr hr1 x hx hxv
  let B := fun z => pullbackEllipticOperator (fderiv ℝ P (F z)) (A (F z))
  let W := fun z => u (F z)
  have hW (z) (hz : z ∈ closedHalfBall v) : ContDiffAt ℝ 2 W z := (hu z hz).comp z (hF z hz)
  have hWD (z) (hz : z ∈ closedHalfBall v) : fderiv ℝ W z =
      (fderiv ℝ u (F z)).comp (fderiv ℝ F z) := by
    exact ((hu z hz).differentiableAt (by norm_num)).hasFDerivAt.comp z
      ((hF z hz).differentiableAt (by norm_num)).hasFDerivAt |>.fderiv
  have hWbound (z) (hz : z ∈ closedHalfBall v) : ‖fderiv ℝ W z‖ ≤ V * V := by
    rw [hWD z hz]
    exact ((fderiv ℝ u (F z)).opNorm_comp_le _).trans
      (mul_le_mul (hDu z hz) (hDF z hz) (norm_nonneg _) hV)
  have hWLu (z) (hz : z ∈ openHalfBall v) : |ellipticTrace B W z| ≤ 2 * K * lam * Fintype.card ι := by
    have hzc : z ∈ closedHalfBall v := ⟨hz.1.le, hz.2.le⟩
    have hh := ellipticTrace_inverse_pullback_bound A (hP z hzc) (hF z hzc) (hu z hzc) (hinv z hzc)
    have hp : Module.finrank ℝ (EuclideanSpace ℝ ι) *
        ‖B z‖ * ‖fderiv ℝ u (F z)‖ * ‖iteratedFDeriv ℝ 2 F z‖ ≤ d * V ^ 3 := by
      have hd' : (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) = d := by simp [d]
      rw [hd']
      calc
        d * ‖B z‖ * ‖fderiv ℝ u (F z)‖ * ‖iteratedFDeriv ℝ 2 F z‖ ≤ d * V * V * V := by
          gcongr
          exact hB z hzc
          exact hDu z hzc
          exact hDDF z hzc
        _ = _ := by ring
    have he : 2 * K * lam * (Fintype.card ι : ℝ) = V + d * V ^ 3 := by
      change 2 * ((V + d * V ^ 3) / (2 * lam * d)) * lam * d = _
      field_simp
    rw [he]
    exact hh.trans (add_le_add (hLu z hz) hp)
  have hslope := boundary_slope_of_gradient v hv
    (fun z hz => (hW z hz).differentiableAt (by norm_num)) hWbound hzero
  have hzmem : z ∈ closedHalfBall v := ⟨by linarith, by simp [hvz]⟩
  have hh := hholder v hv B W hW hslope hlo hhi hWLu z hz hvz r hr hr1 x hx hxv
  rw [hWD z hzmem] at hh
  exact hh

end OAI.Analysis.PDE.Elliptic
