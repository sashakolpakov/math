import OAI.AlgebraicGeometry.Comparison.Betti.VectorDbarHolomorphicPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricDbarKernels

/-! # Punctured Cauchy -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PuncturedCauchy.Dolbeault

noncomputable section

section

/-! The two smooth whole-line inputs used to solve the antiholomorphic
equation on a punctured line, with the exact inversion Jacobian. -/

open _root_.TopologicalSpace Set _root_.Metric Filter
open scoped ContDiff _root_.Topology

def puncturedComplexOpen : Opens ℂ := ⟨{z | z ≠ 0}, isOpen_ne⟩

def puncturedCauchyBump : ContDiffBump (0 : ℂ) :=
  { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

def complexInversionJacobian (z : ℂ) : ℂ := star (-(z ^ 2)⁻¹)

theorem complexInversionJacobian_smoothAt {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ complexInversionJacobian z :=
  Complex.conjCLE.contDiff.contDiffAt.comp z ((contDiffAt_id.pow 2).inv (pow_ne_zero 2 hz)).neg

theorem complexInversionJacobian_inverse_product {z : ℂ} (hz : z ≠ 0) :
    complexInversionJacobian z * complexInversionJacobian z⁻¹ = 1 := by
  unfold complexInversionJacobian
  rw [← star_mul]
  simp only [inv_pow, inv_inv, neg_mul_neg, mul_inv_cancel₀ (pow_ne_zero 2 hz), star_one]

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def puncturedCauchyOuterInput (g : P × ℂ → F) (q : P × ℂ) : F :=
  (1 - (puncturedCauchyBump q.2 : ℂ)) • g q

def puncturedCauchyInnerInput (g : P × ℂ → F) (q : P × ℂ) : F :=
  complexInversionJacobian q.2 • ((puncturedCauchyBump q.2⁻¹ : ℂ) • g (q.1, q.2⁻¹))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem puncturedCauchyOuterInput_zero (g : P × ℂ → F) {q : P × ℂ} (hq : ‖q.2‖ ≤ 1) :
    puncturedCauchyOuterInput g q = 0 := by
  have hone := puncturedCauchyBump.one_of_mem_closedBall
    (show q.2 ∈ closedBall 0 puncturedCauchyBump.rIn by
      simpa only [mem_closedBall, dist_zero_right, puncturedCauchyBump] using hq)
  simp only [puncturedCauchyOuterInput, hone, Complex.ofReal_one, sub_self, zero_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem puncturedCauchyInnerInput_zero (g : P × ℂ → F) {q : P × ℂ} (hq : ‖q.2‖ < 1 / 2) :
    puncturedCauchyInnerInput g q = 0 := by
  by_cases hz : q.2 = 0
  · simp only [puncturedCauchyInnerInput, complexInversionJacobian, hz, zero_pow (by decide : 2 ≠ 0),
      inv_zero, neg_zero, star_zero, zero_smul]
  · have hpos : 0 < ‖q.2‖ := norm_pos_iff.mpr hz
    have hlarge : (2 : ℝ) ≤ 1 / ‖q.2‖ := (le_div_iff₀ hpos).mpr (by linarith)
    have hzero := puncturedCauchyBump.zero_of_le_dist
      (show puncturedCauchyBump.rOut ≤ dist q.2⁻¹ 0 by
        simpa only [dist_zero_right, norm_inv, one_div, puncturedCauchyBump] using hlarge)
    simp only [puncturedCauchyInnerInput, hzero, Complex.ofReal_zero, zero_smul, smul_zero]

theorem puncturedCauchyOuterInput_smooth (S : Opens P) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (puncturedComplexOpen : Set ℂ))) :
    ContDiffOn ℝ ∞ (puncturedCauchyOuterInput g) ((S : Set P) ×ˢ univ) := by
  intro q hq
  by_cases hz : q.2 = 0
  · have hnear : ∀ᶠ y in 𝓝 q, ‖y.2‖ < 1 := by
      have hsnd : Tendsto (Prod.snd : P × ℂ → ℂ) (𝓝 q) (𝓝 (0 : ℂ)) := hz ▸ continuousAt_snd
      filter_upwards [hsnd.eventually (ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 : ℝ)))] with y hy
      simpa only [mem_ball, dist_zero_right] using hy
    apply ((contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hnear] with y hy
    exact puncturedCauchyOuterInput_zero g hy.le
  · have hgp := hg.contDiffAt ((S.isOpen.prod puncturedComplexOpen.isOpen).mem_nhds ⟨hq.1, hz⟩)
    have hχ : ContDiffAt ℝ ∞ (fun y : P × ℂ => (puncturedCauchyBump y.2 : ℂ)) q :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp q (puncturedCauchyBump.contDiff.contDiffAt.comp q contDiffAt_snd)
    exact ((contDiffAt_const.sub hχ).smul hgp).contDiffWithinAt

theorem puncturedCauchyInnerInput_smooth (S : Opens P) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (puncturedComplexOpen : Set ℂ))) :
    ContDiffOn ℝ ∞ (puncturedCauchyInnerInput g) ((S : Set P) ×ˢ univ) := by
  intro q hq
  by_cases hz : q.2 = 0
  · have hnear : ∀ᶠ y in 𝓝 q, ‖y.2‖ < 1 / 2 := by
      have hsnd : Tendsto (Prod.snd : P × ℂ → ℂ) (𝓝 q) (𝓝 (0 : ℂ)) := hz ▸ continuousAt_snd
      filter_upwards [hsnd.eventually (ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 / 2 : ℝ)))] with y hy
      simpa only [mem_ball, dist_zero_right] using hy
    apply ((contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hnear] with y hy
    exact puncturedCauchyInnerInput_zero g hy
  · have hinv : ContDiffAt ℝ ∞ (fun y : P × ℂ => y.2⁻¹) q := contDiffAt_snd.inv hz
    have hgp := (hg.contDiffAt ((S.isOpen.prod puncturedComplexOpen.isOpen).mem_nhds
      (show (q.1, q.2⁻¹) ∈ (S : Set P) ×ˢ (puncturedComplexOpen : Set ℂ) from ⟨hq.1, inv_ne_zero hz⟩))).comp q (contDiffAt_fst.prodMk hinv)
    have hχ : ContDiffAt ℝ ∞ (fun y : P × ℂ => (puncturedCauchyBump y.2⁻¹ : ℂ)) q :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp q (puncturedCauchyBump.contDiff.contDiffAt.comp q hinv)
    have hJ := (complexInversionJacobian_smoothAt hz).comp q contDiffAt_snd
    exact (hJ.smul (hχ.smul hgp)).contDiffWithinAt

end

/-! The extended punctured-line input pieces vanish on neighborhoods
of zero, so their actual full derivatives there are zero. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]

theorem puncturedCauchyOuterInput_fderiv_zero (g : P × ℂ → F) (p : P) :
    fderiv ℝ (puncturedCauchyOuterInput g) (p, 0) = 0 := by
  have he : puncturedCauchyOuterInput g =ᶠ[𝓝 (p, (0 : ℂ))] fun _ => 0 := by
    have hsnd : Tendsto (Prod.snd : P × ℂ → ℂ) (𝓝 (p, (0 : ℂ))) (𝓝 (0 : ℂ)) := continuousAt_snd
    filter_upwards [hsnd.eventually (ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 : ℝ)))] with y hy
    exact puncturedCauchyOuterInput_zero g (by simpa only [mem_ball, dist_zero_right] using hy.le)
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (𝕜 := ℝ) (0 : F) (p, (0 : ℂ))).fderiv

theorem puncturedCauchyInnerInput_fderiv_zero (g : P × ℂ → F) (p : P) :
    fderiv ℝ (puncturedCauchyInnerInput g) (p, 0) = 0 := by
  have he : puncturedCauchyInnerInput g =ᶠ[𝓝 (p, (0 : ℂ))] fun _ => 0 := by
    have hsnd : Tendsto (Prod.snd : P × ℂ → ℂ) (𝓝 (p, (0 : ℂ))) (𝓝 (0 : ℂ)) := continuousAt_snd
    filter_upwards [hsnd.eventually (ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 / 2 : ℝ)))] with y hy
    exact puncturedCauchyInnerInput_zero g (by simpa only [mem_ball, dist_zero_right] using hy)
  rw [he.fderiv_eq]
  exact (hasFDerivAt_const (𝕜 := ℝ) (0 : F) (p, (0 : ℂ))).fderiv

end

end OAI.AlgebraicGeometry.Comparison.Betti.PuncturedCauchy.Dolbeault
