import OAI.Analysis.PDE.Elliptic.Boundary.Translate

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

theorem boundary_centered_first_order_holder
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ m M K : ℝ, m ≤ M → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ closedHalfBall v, m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall v, |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∀ z, ‖z‖ ≤ 1 / 4 → inner ℝ v z = 0 →
      ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, ‖x - z‖ ≤ r / 2 → 0 ≤ inner ℝ v x →
        |u x - (fderiv ℝ u z v) * inner ℝ v x| ≤ C * r ^ α * inner ℝ v x := by
  obtain ⟨α, hα, hα1, hholder⟩ := boundary_first_order_holder (ι := ι) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro m M K hmM hK
  obtain ⟨C, hC, hCbound⟩ := hholder m M K hmM hK
  refine ⟨C, hC, ?_⟩
  intro v hv A u hu hbound hlo hhi hLu z hz hzv
  let w := fun y => (1 / 2 : ℝ)⁻¹ * u (z + (1 / 2 : ℝ) • y)
  let Az := fun y => A (z + (1 / 2 : ℝ) • y)
  have hw : ContDiff ℝ 2 w :=
    contDiff_const.mul (hu.comp (contDiff_const.add (contDiff_id.const_smul _)))
  have hh (y : EuclideanSpace ℝ ι) : inner ℝ v (z + (1 / 2 : ℝ) • y) = inner ℝ v y / 2 := by
    rw [inner_add_right, hzv, real_inner_smul_right]; ring
  have hn (y : EuclideanSpace ℝ ι) (hy : ‖y‖ ≤ 1) : ‖z + (1 / 2 : ℝ) • y‖ < 1 := by
    have hb := norm_add_le z ((1 / 2 : ℝ) • y)
    rw [norm_smul] at hb
    norm_num at hb
    linarith
  have hclosed (y : EuclideanSpace ℝ ι) (hy : y ∈ closedHalfBall v) :
      z + (1 / 2 : ℝ) • y ∈ closedHalfBall v :=
    ⟨(hn y hy.1).le, by rw [hh]; exact div_nonneg hy.2 (by norm_num)⟩
  have hopen (y : EuclideanSpace ℝ ι) (hy : y ∈ openHalfBall v) :
      z + (1 / 2 : ℝ) • y ∈ openHalfBall v :=
    ⟨hn y hy.1.le, by rw [hh]; exact div_pos hy.2 (by norm_num)⟩
  have hwb (y : EuclideanSpace ℝ ι) (hy : y ∈ closedHalfBall v) :
      m * inner ℝ v y ≤ w y ∧ w y ≤ M * inner ℝ v y := by
    have hb := hbound _ (hclosed y hy)
    rw [hh] at hb
    dsimp [w]
    norm_num
    constructor <;> nlinarith [hb.1, hb.2]
  have hwL (y : EuclideanSpace ℝ ι) (hy : y ∈ openHalfBall v) :
      |ellipticTrace Az w y| ≤ 2 * K * lam * Fintype.card ι := by
    have ht := ellipticTrace_slope_rescale_center A hu z (by norm_num : (1 / 2 : ℝ) ≠ 0) y
    change ellipticTrace Az w y = _ at ht
    rw [ht, abs_mul]
    norm_num
    have hb := hLu _ (hopen y hy)
    nlinarith [abs_nonneg (ellipticTrace A u (z + (1 / 2 : ℝ) • y))]
  have hD : fderiv ℝ w 0 v = fderiv ℝ u z v := by
    simpa only [smul_zero, add_zero] using
      fderiv_slope_rescale_center hu z (by norm_num : (1 / 2 : ℝ) ≠ 0) 0 v
  have hresult := hCbound v hv Az w hw hwb
    (fun y hy => hlo _ (hclosed y hy)) (fun y hy => hhi _ (hclosed y hy)) hwL
  intro r hr hr1 x hx htx
  let y := (2 : ℝ) • (x - z)
  have hyn : ‖y‖ ≤ r := by dsimp [y]; rw [norm_smul]; norm_num; linarith
  have hyh : inner ℝ v y = 2 * inner ℝ v x := by
    dsimp [y]; rw [real_inner_smul_right, inner_sub_right, hzv]; ring
  have hypos : 0 ≤ inner ℝ v y := by rw [hyh]; positivity
  have hypoint : z + (1 / 2 : ℝ) • y = x := by dsimp [y]; module
  have hb := hresult r hr hr1 y hyn hypos
  rw [hD, hyh] at hb
  dsimp [w] at hb
  rw [hypoint] at hb
  norm_num at hb
  have he : 2 * u x - (fderiv ℝ u z) v * (2 * inner ℝ v x) =
      2 * (u x - (fderiv ℝ u z) v * inner ℝ v x) := by ring
  rw [he, abs_mul] at hb
  norm_num at hb
  nlinarith

end OAI.Analysis.PDE.Elliptic
