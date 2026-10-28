import OAI.Analysis.PDE.Elliptic.Boundary.HalfBallPair

/-! Strict boundary slope-interval contraction for an actual linear elliptic
equation with bounded forcing.  No Harnack or barrier estimate is assumed. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

section LinearHeight
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem gradient_linear_height (v : E) : gradient (fun x => inner ℝ v x) = fun _ => v := by
  funext x
  change (toDual ℝ E).symm (fderiv ℝ (toDual ℝ E v) x) = v
  rw [(toDual ℝ E v).fderiv]
  exact (toDual ℝ E).symm_apply_apply v

theorem ellipticTrace_linear_height (A : E → E →L[ℝ] E) (v x : E) :
    ellipticTrace A (fun y => inner ℝ v y) x = 0 := by
  unfold ellipticTrace
  rw [gradient_linear_height]
  simp

theorem ellipticTrace_sub_linear_height (A : E → E →L[ℝ] E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (v : E) (m : ℝ) (x : E) :
    ellipticTrace A (fun y => u y - m * inner ℝ v y) x = ellipticTrace A u x := by
  have hh : ContDiff ℝ 2 (fun y => inner ℝ v y) := (toDual ℝ E v).contDiff
  have he : (fun y => u y - m * inner ℝ v y) = fun y => u y + (-m) • inner ℝ v y := by
    funext y; simp [sub_eq_add_neg]
  rw [he, ellipticTrace_add_smul A hu hh, ellipticTrace_linear_height]
  ring

theorem ellipticTrace_linear_height_sub (A : E → E →L[ℝ] E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (v : E) (m : ℝ) (x : E) :
    ellipticTrace A (fun y => m * inner ℝ v y - u y) x = -ellipticTrace A u x := by
  have hh : ContDiff ℝ 2 (fun y => inner ℝ v y) := (toDual ℝ E v).contDiff
  have hn : ContDiff ℝ 2 (fun y => (0 : ℝ) - u y) := contDiff_const.sub hu
  have he : (fun y => m * inner ℝ v y - u y) = fun y => (0 - u y) + m • inner ℝ v y := by
    funext y; simp only [smul_eq_mul]; ring
  rw [he, ellipticTrace_add_smul A hn hh, ellipticTrace_linear_height,
    ellipticTrace_const_sub A hu]
  ring
end LinearHeight

theorem boundary_slope_contraction
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ r θ C : ℝ, 0 < r ∧ r < 1 ∧ 0 < θ ∧ θ < 1 ∧ 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (K m M : ℝ), 0 ≤ K → m ≤ M →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ closedHalfBall v, m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall v, |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∃ m' M' : ℝ, m ≤ m' ∧ m' ≤ M' ∧ M' ≤ M ∧
        M' - m' ≤ (1 - θ) * (M - m) + C * K ∧
        ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
          m' * inner ℝ v x ≤ u x ∧ u x ≤ M' * inner ℝ v x := by
  classical
  obtain ⟨r, q, C, hr, hr1, hq, hC, hpair⟩ := half_ball_pair_lower (ι := ι) hlam hL
  let θ := min q (1 / 2)
  have ht : 0 < θ := lt_min hq (by norm_num)
  have htq : θ ≤ q := min_le_left _ _
  have ht1 : θ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨r, θ, C, hr, hr1, ht, ht1, hC, ?_⟩
  intro v hv K m M hK hmM A u hu hbound hlo hhi hLu
  let w : Fin 2 → EuclideanSpace ℝ ι → ℝ :=
    ![fun x => u x - m * inner ℝ v x, fun x => M * inner ℝ v x - u x]
  have hh : ContDiff ℝ 2 (fun y => inner ℝ v y) := (toDual ℝ (EuclideanSpace ℝ ι) v).contDiff
  have hw (j : Fin 2) : ContDiff ℝ 2 (w j) := by
    fin_cases j
    · exact hu.sub (contDiff_const.mul hh)
    · exact (contDiff_const.mul hh).sub hu
  have hwpos (j : Fin 2) (x : EuclideanSpace ℝ ι) (hx : x ∈ closedHalfBall v) : 0 ≤ w j x := by
    have hh := hbound x hx
    fin_cases j <;> dsimp [w] <;> linarith
  have hweq (j : Fin 2) (x : EuclideanSpace ℝ ι) (hx : x ∈ openHalfBall v) :
      ellipticTrace A (w j) x ≤ 2 * K * lam * Fintype.card ι := by
    have hh := abs_le.mp (hLu x hx)
    fin_cases j
    · change ellipticTrace A (fun y => u y - m * inner ℝ v y) x ≤ _
      rw [ellipticTrace_sub_linear_height A hu]
      exact hh.2
    · change ellipticTrace A (fun y => M * inner ℝ v y - u y) x ≤ _
      rw [ellipticTrace_linear_height_sub A hu]
      linarith
  obtain ⟨j, hj⟩ := hpair v hv K (M - m) hK (sub_nonneg.mpr hmM)
    (fun _ => A) w hw hwpos (fun _ => hlo) (fun _ => hhi) hweq
    (fun x _ => by dsimp [w]; ring_nf; rfl)
  let δ := max (θ * (M - m) - C * K) 0
  have hd0 : 0 ≤ δ := le_max_right _ _
  have hdW : δ ≤ M - m := by
    apply max_le
    · have hh := mul_le_mul_of_nonneg_right ht1.le (sub_nonneg.mpr hmM)
      nlinarith [mul_nonneg hC.le hK]
    · linarith
  have hdcore : θ * (M - m) - C * K ≤ δ := le_max_left _ _
  have hsmall (x : EuclideanSpace ℝ ι) (hx : ‖x‖ ≤ r) (htx : 0 ≤ inner ℝ v x) :
      x ∈ closedHalfBall v := ⟨hx.trans hr1.le, htx⟩
  have hraise (x : EuclideanSpace ℝ ι) (hx : ‖x‖ ≤ r) (htx : 0 ≤ inner ℝ v x) :
      δ * inner ℝ v x ≤ w j x := by
    by_cases hcore : 0 ≤ θ * (M - m) - C * K
    · have hd : δ = θ * (M - m) - C * K := max_eq_left hcore
      rw [hd]
      apply le_trans _ (hj x hx htx)
      apply mul_le_mul_of_nonneg_right _ htx
      exact sub_le_sub_right (mul_le_mul_of_nonneg_right htq (sub_nonneg.mpr hmM)) _
    · have hd : δ = 0 := max_eq_right (le_of_not_ge hcore)
      rw [hd, zero_mul]
      exact hwpos j x (hsmall x hx htx)
  fin_cases j
  · refine ⟨m + δ, M, by linarith, by linarith, le_refl _, by nlinarith, ?_⟩
    intro x hx htx
    have hb := hbound x (hsmall x hx htx)
    have hh := hraise x hx htx
    dsimp [w] at hh
    constructor <;> nlinarith
  · refine ⟨m, M - δ, le_refl _, by linarith, by linarith, by nlinarith, ?_⟩
    intro x hx htx
    have hb := hbound x (hsmall x hx htx)
    have hh := hraise x hx htx
    dsimp [w] at hh
    constructor <;> nlinarith

end OAI.Analysis.PDE.Elliptic
