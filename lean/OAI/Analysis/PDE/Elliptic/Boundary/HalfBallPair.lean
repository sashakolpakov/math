import OAI.Analysis.PDE.Elliptic.Boundary.HalfBall
import OAI.Analysis.PDE.Elliptic.Boundary.HarnackPair
import OAI.Analysis.PDE.Elliptic.Evans.CenteredCube

/-! A quantitative boundary alternative obtained from actual weak Harnack
and actual annular barriers.  The constants precede the operators/functions. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace BoxIntegral

theorem half_ball_pair_lower
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ r q C : ℝ, 0 < r ∧ r < 1 ∧ 0 < q ∧ 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (K s : ℝ), 0 ≤ K → 0 ≤ s →
      ∀ (A : Fin 2 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : Fin 2 → EuclideanSpace ℝ ι → ℝ),
      (∀ j, ContDiff ℝ 2 (u j)) →
      (∀ j, ∀ x ∈ closedHalfBall v, 0 ≤ u j x) →
      (∀ j, ∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A j x w)) →
      (∀ j, ∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A j x w) ≤ L * ‖w‖ ^ 2) →
      (∀ j, ∀ x ∈ openHalfBall v,
        ellipticTrace (A j) (u j) x ≤ 2 * K * lam * Fintype.card ι) →
      (∀ x ∈ closedHalfBall v, s * inner ℝ v x ≤ u 0 x + u 1 x) →
      ∃ j : Fin 2, ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
        (q * s - C * K) * inner ℝ v x ≤ u j x := by
  classical
  obtain ⟨c, hc, hpair⟩ := weak_harnack_pair_lower (ι := ι) hlam hL
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  let r : ℝ := 1 / (1024 * (d + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : 1024 * (d + 1) * r = 1 := by dsimp [r]; field_simp
  have hrsmall : r ≤ 1 / 1024 := by nlinarith [mul_pos hd hr]
  let H := 32 * d * r
  have hH : 0 < H := by dsimp [H]; positivity
  have hHsmall : H ≤ 1 / 8 := by dsimp [H]; nlinarith
  let a := L * d / (lam * r ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hae : a * (lam * r ^ 2) = L * d := div_mul_cancel₀ _ (by positivity)
  let P := a * (1 / 4) * Real.exp (-a * (1 / 4) ^ 2)
  have hP : 0 < P := by dsimp [P]; positivity
  let q := c / 8 * P
  let C := H ^ 2 * P + 1 / 2
  refine ⟨r, q, C, hr, by linarith, by dsimp [q]; positivity,
    by dsimp [C]; positivity, ?_⟩
  intro v hv K s hK hs A u hu hpos hlo hhi hLu hsum
  let z := (1 / 4 : ℝ) • v
  let B := centeredCube z (4 * r) (by positivity)
  have hz : ‖z‖ = 1 / 4 := by simp [z, norm_smul, hv]
  have hzv : inner ℝ v z = 1 / 4 := by simp [z, real_inner_smul_right, hv]
  have hcenter : cubeCenter B = z := centeredCube_center z (by positivity)
  have hheight (x : EuclideanSpace ℝ ι) (hx : x ∈ Metric.closedBall z H) :
      1 / 8 ≤ inner ℝ v x := by
    have hdist : ‖x - z‖ ≤ H := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hinner := abs_real_inner_le_norm v (x - z)
    rw [hv, one_mul, inner_sub_right, hzv, abs_le] at hinner
    linarith [hinner.1]
  have hnorm (x : EuclideanSpace ℝ ι) (hx : x ∈ Metric.closedBall z H) : ‖x‖ < 1 := by
    have hdist : ‖x - z‖ ≤ H := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hh := norm_add_le (x - z) z
    rw [sub_add_cancel] at hh
    linarith
  have hclosed (x : EuclideanSpace ℝ ι) (hx : x ∈ Metric.closedBall z H) :
      x ∈ closedHalfBall v := ⟨(hnorm x hx).le, (by linarith [hheight x hx])⟩
  have hopen (x : EuclideanSpace ℝ ι) (hx : x ∈ Metric.ball z H) :
      x ∈ openHalfBall v :=
    ⟨hnorm x (Metric.ball_subset_closedBall hx), by linarith [hheight x (Metric.ball_subset_closedBall hx)]⟩
  have hrad : 8 * (Fintype.card ι : ℝ) * (4 * r) = H := by dsimp [H, d]; ring
  have hQ : euclideanBox B ⊆ Metric.closedBall z H := by
    have hh := euclideanBox_subset_closedBall B (by positivity : (0 : ℝ) ≤ 4 * r)
      (centeredCube_width z (by positivity))
    rw [hcenter] at hh
    apply hh.trans
    apply Metric.closedBall_subset_closedBall
    dsimp [H, d]
    nlinarith [mul_pos hd hr]
  obtain ⟨j, hj⟩ := hpair B (4 * r) K (s / 8) (by positivity) hK
    (centeredCube_width z (by positivity)) A u hu
    (fun j x hx => hpos j x (hclosed x (by simpa only [hcenter, hrad] using hx)))
    (fun j x hx => hlo j x (hclosed x (by simpa only [hcenter, hrad] using hx)))
    (fun j x hx => hhi j x (hclosed x (by simpa only [hcenter, hrad] using hx)))
    (fun j x hx => hLu j x (hopen x (by simpa only [hcenter, hrad] using hx)))
    (fun x hx => (by
      have hh := mul_le_mul_of_nonneg_left (hheight x (hQ hx)) hs
      exact (by nlinarith : s / 8 ≤ s * inner ℝ v x).trans (hsum x (hclosed x (hQ hx)))))
  let l := max (c * (s / 8) - K * H ^ 2) 0
  have hl : 0 ≤ l := le_max_right _ _
  have hinner : ∀ x ∈ Metric.closedBall z (2 * r), l ≤ u j x := by
    intro x hx
    have hxQ : x ∈ euclideanBox B := by
      have hh := closedBall_subset_centeredCube z (by positivity : (0 : ℝ) < 2 * r) hx
      convert hh using 1 ; simp only [B]; congr 2 ; ring
    apply max_le
    · simpa only [hrad] using hj x hxQ
    · exact hpos j x (hclosed x (hQ hxQ))
  have hhopf := half_ball_hopf_lower v hv (A j) (hu j) ha.le
    (by norm_num : (0 : ℝ) < 1 / 4) (le_refl _) hr (by linarith)
    hl hK hlam (by simpa only [finrank_euclideanSpace] using (by nlinarith [hae] : L * d ≤ 2 * a * lam * r ^ 2))
    (hpos j) (hlo j) (hhi j)
    (by simpa only [finrank_euclideanSpace] using hLu j) hinner
  refine ⟨j, ?_⟩
  intro x hx ht
  have hcoeff : q * s - C * K ≤ l * a * (1 / 4) * Real.exp (-a * (1 / 4) ^ 2) - 2 * K * (1 / 4) := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left (c * (s / 8) - K * H ^ 2) 0) hP.le
    dsimp only [q, C, l, P] at *
    nlinarith
  exact (mul_le_mul_of_nonneg_right hcoeff ht).trans (hhopf x hx ht)

end OAI.Analysis.PDE.Elliptic
