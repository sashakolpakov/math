import OAI.Analysis.PDE.Elliptic.CubeGrowth
import OAI.Analysis.PDE.Elliptic.CubeDomains

open Set BoxIntegral _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem cube_density_toReal (B : Box ι) {theta : ℝ} (htheta : 0 ≤ theta)
    {S : Set (EuclideanSpace ℝ ι)} (hS : S ⊆ euclideanBox B)
    (h : ENNReal.ofReal theta * volume (euclideanBox B) < volume S) :
    theta * volume.real (euclideanBox B) < volume.real S := by
  have hB : volume (euclideanBox B) ≠ ⊤ := by
    rw [volume_euclideanBox]
    exact (B.measure_coe_lt_top volume).ne
  have hSf : volume S ≠ ⊤ := ne_of_lt ((measure_mono hS).trans_lt hB.lt_top)
  have hprod : ENNReal.ofReal theta * volume (euclideanBox B) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  have hreal := (ENNReal.toReal_lt_toReal hprod hSf).mpr h
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal htheta] using hreal

/-- Uniform one-step decay of superlevel measure for a nonnegative
elliptic supersolution. All covering and growth ingredients are proved. -/
theorem uniform_superlevel_measure_decay {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ M theta : ℝ, 1 < M ∧ 0 < theta ∧ theta < 1 ∧
      ∀ (B : Box ι) (R : ℝ), 0 < R →
      (∀ i, B.upper i - B.lower i = 2 * R) →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), 0 ≤ u x) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ v,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ Metric.closedBall (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R), ∀ v,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.ball (cubeCenter B) (8 * (Fintype.card ι : ℝ) * R),
        ellipticTrace A u x ≤ 0) →
      (∃ x ∈ euclideanBox B, u x ≤ 1) →
      ∀ t : ℝ, 1 ≤ t →
      volume ({x | t * M < u x} ∩ euclideanBox B) ≤
        ENNReal.ofReal theta * volume ({x | t < u x} ∩ euclideanBox B) := by
  obtain ⟨M, eta, hM, heta, heta1, hg⟩ := cube_superlevel_ball (ι := ι) hlam hL
  have htpos : 0 < 1 - eta := sub_pos.mpr heta1
  have htlt : 1 - eta < 1 := by linarith
  refine ⟨M, 1 - eta, hM, htpos, htlt, ?_⟩
  intro B R hR hB A u hu hnonneg hlo hhi hLu hx0 t ht
  have ht' : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hdomain := cube_growth_domain_subset (B := B) (C := B) le_rfl hR hR hB hB
  have hroot : volume ({x | t * M < u x} ∩ euclideanBox B) ≤
      ENNReal.ofReal (1 - eta) * volume (euclideanBox B) := by
    by_contra hn
    have hdensity := cube_density_toReal B htpos.le inter_subset_right (lt_of_not_ge hn)
    rw [inter_comm] at hdensity
    have hpoint := hg B R t hR ht' hB A u hu
      (fun x hx ↦ hnonneg x (Metric.ball_subset_closedBall (hdomain hx)))
      (fun x hx ↦ hlo x (Metric.ball_subset_closedBall (hdomain hx)))
      (fun x hx ↦ hhi x (Metric.ball_subset_closedBall (hdomain hx)))
      (fun x hx ↦ hLu x (hdomain (Metric.ball_subset_closedBall hx))) hdensity
    obtain ⟨x0, hx0, hu0⟩ := hx0
    have hrad : (Fintype.card ι : ℝ) * R ≤ 3 * (Fintype.card ι : ℝ) * R := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _) hR.le]
    have hmem := Metric.closedBall_subset_closedBall hrad
      (euclideanBox_subset_closedBall B hR.le hB hx0)
    exact (not_lt_of_ge (hu0.trans ht)) (hpoint x0 hmem)
  apply euclidean_dyadic_open_cover B (isOpen_lt continuous_const hu.continuous)
    ((isOpen_lt continuous_const hu.continuous).measurableSet.inter (measurableSet_euclideanBox B))
    (ENNReal.ofReal_lt_one.mpr htlt) hroot
  intro w s hdensity x hx
  let P := dyadicBox B w
  let C := P.splitCenterBox s
  let r : ℝ := R / 2 ^ (w.length + 1)
  have hr : 0 < r := div_pos hR (by positivity)
  have hP : ∀ i, P.upper i - P.lower i = 4 * r := dyadicBox_parent_halfwidth B hB w
  have hC : ∀ i, C.upper i - C.lower i = 2 * r := splitCenterBox_halfwidth P hP s
  have hCB : C ≤ B := (P.splitCenterBox_le s).trans (dyadicBox_le B w)
  have hdom := cube_growth_domain_subset hCB hr hR hC hB
  have hreal := cube_density_toReal C htpos.le inter_subset_right hdensity
  rw [inter_comm] at hreal
  have hpoint := hg C r t hr ht' hC A u hu
    (fun x hx ↦ hnonneg x (Metric.ball_subset_closedBall (hdom hx)))
    (fun x hx ↦ hlo x (Metric.ball_subset_closedBall (hdom hx)))
    (fun x hx ↦ hhi x (Metric.ball_subset_closedBall (hdom hx)))
    (fun x hx ↦ hLu x (hdom (Metric.ball_subset_closedBall hx))) hreal
  exact ⟨hpoint x (parent_subset_child_ball P hr.le hP s hx),
    euclideanBox_mono (dyadicBox_le B w) hx⟩

end OAI.Analysis.PDE.Elliptic
