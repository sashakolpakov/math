import OAI.Analysis.PDE.Elliptic.Boundary.Slope

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

theorem ellipticTrace_slope_rescale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E) {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {R : ℝ} (hR : R ≠ 0) (x : E) :
    ellipticTrace (fun y => A (R • y)) (fun y => R⁻¹ * u (R • y)) x =
      R * ellipticTrace A u (R • x) := by
  have hh : ContDiff ℝ 2 (fun y : E => u (R • y)) := hu.comp (contDiff_id.const_smul R)
  have hs := ellipticTrace_smul (fun y => A (R • y)) hh R⁻¹ x
  simp only [smul_eq_mul] at hs
  rw [hs]
  have he := ellipticTrace_rescalePoint A hu (0 : E) R x
  simp only [rescalePoint, zero_add] at he
  rw [he]
  field_simp

theorem boundary_slope_contraction_scaled
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ ρ θ C : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < θ ∧ θ < 1 ∧ 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (R K m M : ℝ), 0 < R → 0 ≤ K → m ≤ M →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x, ‖x‖ ≤ R → 0 ≤ inner ℝ v x → m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x, ‖x‖ ≤ R → 0 ≤ inner ℝ v x → ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x, ‖x‖ ≤ R → 0 ≤ inner ℝ v x → ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x, ‖x‖ < R → 0 < inner ℝ v x → |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∃ m' M' : ℝ, m ≤ m' ∧ m' ≤ M' ∧ M' ≤ M ∧
        M' - m' ≤ (1 - θ) * (M - m) + C * K * R ∧
        ∀ x, ‖x‖ ≤ ρ * R → 0 ≤ inner ℝ v x →
          m' * inner ℝ v x ≤ u x ∧ u x ≤ M' * inner ℝ v x := by
  obtain ⟨ρ, θ, C, hρ, hρ1, ht, ht1, hC, hstep⟩ := boundary_slope_contraction (ι := ι) hlam hL
  refine ⟨ρ, θ, C, hρ, hρ1, ht, ht1, hC, ?_⟩
  intro v hv R K m M hR hK hmM A u hu hbound hlo hhi hLu
  let ur := fun x : EuclideanSpace ℝ ι => R⁻¹ * u (R • x)
  have hur : ContDiff ℝ 2 ur := contDiff_const.mul (hu.comp (contDiff_id.const_smul R))
  have hnorm (x : EuclideanSpace ℝ ι) : ‖R • x‖ = R * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hheight (x : EuclideanSpace ℝ ι) : inner ℝ v (R • x) = R * inner ℝ v x :=
    real_inner_smul_right _ _ _
  have hclosed (x : EuclideanSpace ℝ ι) (hx : x ∈ closedHalfBall v) :
      ‖R • x‖ ≤ R ∧ 0 ≤ inner ℝ v (R • x) := by
    rw [hnorm, hheight]
    exact ⟨by nlinarith [hx.1], mul_nonneg hR.le hx.2⟩
  obtain ⟨m', M', hml, hmM', hMu, hwidth, hnew⟩ := hstep v hv (K * R) m M
    (mul_nonneg hK hR.le) hmM (fun x => A (R • x)) ur hur
    (fun x hx => by
      have hh := hbound (R • x) (hclosed x hx).1 (hclosed x hx).2
      rw [hheight] at hh
      dsimp [ur]
      constructor
      · have h := mul_le_mul_of_nonneg_left hh.1 (inv_nonneg.mpr hR.le)
        simpa [← mul_assoc, mul_right_comm R⁻¹ m R, hR.ne'] using h
      · have h := mul_le_mul_of_nonneg_left hh.2 (inv_nonneg.mpr hR.le)
        simpa [← mul_assoc, mul_right_comm R⁻¹ M R, hR.ne'] using h)
    (fun x hx => hlo (R • x) (hclosed x hx).1 (hclosed x hx).2)
    (fun x hx => hhi (R • x) (hclosed x hx).1 (hclosed x hx).2)
    (fun x hx => by
      have hh := hLu (R • x) (by rw [hnorm]; nlinarith [hx.1])
        (by rw [hheight]; exact mul_pos hR hx.2)
      rw [ellipticTrace_slope_rescale _ hu hR.ne', abs_mul, abs_of_pos hR]
      nlinarith)
  refine ⟨m', M', hml, hmM', hMu, by nlinarith [hwidth], ?_⟩
  intro x hx htx
  have hy : ‖R⁻¹ • x‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by nlinarith)
  have hty : 0 ≤ inner ℝ v (R⁻¹ • x) := by
    rw [real_inner_smul_right]; exact mul_nonneg (inv_nonneg.mpr hR.le) htx
  have hh := hnew (R⁻¹ • x) hy hty
  dsimp [ur] at hh
  simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, real_inner_smul_right] at hh
  constructor
  · have h := mul_le_mul_of_nonneg_left hh.1 hR.le
    simpa [← mul_assoc, hR.ne', mul_comm R m'] using h
  · have h := mul_le_mul_of_nonneg_left hh.2 hR.le
    simpa [← mul_assoc, hR.ne', mul_comm R M'] using h

end OAI.Analysis.PDE.Elliptic
