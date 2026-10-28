import OAI.Analysis.PDE.Elliptic.Evans.CenteredCube

open Set Metric BoxIntegral
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J] [Nonempty J]

/-- The cube weak-Harnack argument applied to the actual extrema on concentric
closed balls. The scale ratio depends only on the ambient dimension. -/
theorem ball_oscillation_contraction {lam L δ C F : ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C) (hF : 0 ≤ F) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ (z : EuclideanSpace ℝ ι) (r K : ℝ), 0 < r → 0 ≤ K →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (w : J → EuclideanSpace ℝ ι → ℝ),
      (∀ j, ContDiff ℝ 2 (w j)) →
      (∀ x ∈ closedBall z (16 * (Fintype.card ι : ℝ) * r), ∀ v,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ closedBall z (16 * (Fintype.card ι : ℝ) * r), ∀ v,
        inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ j x, x ∈ ball z (16 * (Fintype.card ι : ℝ) * r) →
        -(2 * K * lam * Fintype.card ι) ≤ ellipticTrace A (w j) x) →
      (∀ x ∈ closedBall z (16 * (Fintype.card ι : ℝ) * r),
        ∀ y ∈ closedBall z (16 * (Fintype.card ι : ℝ) * r),
        ∃ a : J → ℝ, (∀ j, δ ≤ a j ∧ a j ≤ C) ∧
          -(F * r) ≤ ∑ j, a j * (w j x - w j y)) →
      familyOscillation w z r ≤ θ * familyOscillation w z (16 * (Fintype.card ι : ℝ) * r) +
        (2 * r + K * (16 * (Fintype.card ι : ℝ) * r) ^ 2) := by
  classical
  obtain ⟨θ, hθ, hθ1, hc⟩ := cube_oscillation_contraction (ι := ι) (J := J)
    hlam hL hδ hC hF
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro z r K hr hK A w hw hlo hhi hsource hrel
  let d : ℝ := Fintype.card ι
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hrr : r ≤ 16 * d * r := by nlinarith
  let B := centeredCube z (2 * r) (by positivity)
  have hcenter : cubeCenter B = z := centeredCube_center z (by positivity)
  have hrad : 8 * (Fintype.card ι : ℝ) * (2 * r) = 16 * d * r := by dsimp [d]; ring
  have hQ : euclideanBox B ⊆ closedBall z (16 * d * r) := by
    have h := euclideanBox_subset_closedBall B (by positivity : 0 ≤ 2 * r)
      (centeredCube_width z (by positivity))
    rw [hcenter] at h
    apply h.trans (closedBall_subset_closedBall ?_)
    change d * (2 * r) ≤ 16 * d * r
    nlinarith
  have hsmall : closedBall z r ⊆ euclideanBox B := closedBall_subset_centeredCube z hr
  have hlevels (j : J) :
      ballLower (w j) z (16 * d * r) ≤ ballLower (w j) z r ∧
      ballLower (w j) z r ≤ ballUpper (w j) z r ∧
      ballUpper (w j) z r ≤ ballUpper (w j) z (16 * d * r) := by
    obtain ⟨hm, hM⟩ := ball_extrema_mono (hw j).continuous z hr.le hrr
    obtain ⟨hl, hu⟩ := ballLower_le_le_ballUpper (hw j).continuous
      (show z ∈ closedBall z r by simp [hr.le])
    exact ⟨hm, hl.trans hu, hM⟩
  have hout (j : J) (x) (hx : x ∈ closedBall (cubeCenter B)
      (8 * (Fintype.card ι : ℝ) * (2 * r))) :
      ballLower (w j) z (16 * d * r) ≤ w j x ∧
        w j x ≤ ballUpper (w j) z (16 * d * r) := by
    rw [hcenter, hrad] at hx
    exact ballLower_le_le_ballUpper (hw j).continuous hx
  have hmax (j : J) : ∃ x ∈ euclideanBox B, w j x = ballUpper (w j) z r := by
    obtain ⟨x, hx, heq⟩ := exists_ballUpper (hw j).continuous z hr.le
    exact ⟨x, hsmall hx, heq⟩
  have hmin (j : J) : ∃ x ∈ euclideanBox B, w j x = ballLower (w j) z r := by
    obtain ⟨x, hx, heq⟩ := exists_ballLower (hw j).continuous z hr.le
    exact ⟨x, hsmall hx, heq⟩
  have hcoupled (x) (hx : x ∈ euclideanBox B) (y) (hy : y ∈ euclideanBox B) :
      ∃ a : J → ℝ, (∀ j, δ ≤ a j ∧ a j ≤ C) ∧
        -(F * (2 * r)) ≤ ∑ j, a j * (w j x - w j y) := by
    obtain ⟨a, ha, hxy⟩ := hrel x (hQ hx) y (hQ hy)
    refine ⟨a, ha, ?_⟩
    nlinarith [mul_nonneg hF hr.le]
  have h := hc B (2 * r) K (by positivity) hK (centeredCube_width z (by positivity))
    A w (fun j ↦ ballUpper (w j) z (16 * d * r))
      (fun j ↦ ballLower (w j) z (16 * d * r))
      (fun j ↦ ballUpper (w j) z r) (fun j ↦ ballLower (w j) z r) hw
      (by simpa only [hcenter, hrad] using hlo)
      (by simpa only [hcenter, hrad] using hhi) hout
      (by simpa only [hcenter, hrad] using hsource) hlevels hmax hmin hcoupled
  simpa only [familyOscillation, hrad, d] using h

end OAI.Analysis.PDE.Elliptic
