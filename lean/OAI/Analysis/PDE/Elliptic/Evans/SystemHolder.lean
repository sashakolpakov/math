import OAI.Analysis.PDE.Elliptic.Evans.BallOscillation
import OAI.Analysis.PDE.Elliptic.Evans.HolderDecay

open Set Metric
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J] [Nonempty J]

/-- Quantitative interior Hölder oscillation for a positively coupled finite
family of genuine elliptic subsolutions. All constants precede the solution. -/
theorem elliptic_system_holder_oscillation {lam L δ C F K V : ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hV : 0 ≤ V) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ (z : EuclideanSpace ℝ ι)
        (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (w : J → EuclideanSpace ℝ ι → ℝ),
      (∀ j, ContDiff ℝ 2 (w j)) →
      (∀ x ∈ closedBall z 1, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ closedBall z 1, ∀ v, inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) →
      (∀ j x, x ∈ ball z 1 → -(2 * K * lam * Fintype.card ι) ≤ ellipticTrace A (w j) x) →
      (∀ x ∈ closedBall z 1, ∀ y ∈ closedBall z 1,
        ∃ a : J → ℝ, (∀ j, δ ≤ a j ∧ a j ≤ C) ∧
          -(F * dist x y) ≤ ∑ j, a j * (w j x - w j y)) →
      familyOscillation w z 1 ≤ V →
      ∀ r, 0 < r → r ≤ 1 → familyOscillation w z r ≤ B * r ^ α := by
  let d : ℝ := Fintype.card ι
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hd0 : 0 < d := by linarith
  let ρ := 1 / (16 * d)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    apply (div_lt_one (by positivity : 0 < 16 * d)).mpr
    linarith
  have hradius (r : ℝ) : 16 * (Fintype.card ι : ℝ) * (ρ * r) = r := by
    dsimp [ρ, d]
    field_simp
  obtain ⟨θ, hθ, hθ1, hstep⟩ := ball_oscillation_contraction (ι := ι) (J := J)
    hlam hL hδ hC (show 0 ≤ 32 * d * F by positivity)
  obtain ⟨α, hα, hα1, hhold⟩ := holder_decay_of_oscillation_contraction hρ hρ1 hθ.le hθ1
  obtain ⟨B, hB, hbound⟩ := hhold V (2 * ρ + K) hV (by positivity)
  refine ⟨α, B, hα, hα1, hB, ?_⟩
  intro z A w hw hlo hhi hsource hrel hstart
  apply hbound (familyOscillation w z) hstart
    (fun r s hr hrs _ ↦ familyOscillation_mono (fun j ↦ (hw j).continuous) z hr.le hrs)
  intro r hr hr1
  have hc : closedBall z r ⊆ closedBall z 1 := closedBall_subset_closedBall hr1
  have hb : ball z r ⊆ ball z 1 := ball_subset_ball hr1
  have hcoupled (x) (hx : x ∈ closedBall z (16 * (Fintype.card ι : ℝ) * (ρ * r)))
      (y) (hy : y ∈ closedBall z (16 * (Fintype.card ι : ℝ) * (ρ * r))) :
      ∃ a : J → ℝ, (∀ j, δ ≤ a j ∧ a j ≤ C) ∧
        -((32 * d * F) * (ρ * r)) ≤ ∑ j, a j * (w j x - w j y) := by
    rw [hradius] at hx hy
    obtain ⟨a, ha, hxy⟩ := hrel x (hc hx) y (hc hy)
    have hdist : dist x y ≤ 2 * r := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ ≤ r + r := add_le_add hx (by simpa only [mem_closedBall, dist_comm] using hy)
        _ = 2 * r := by ring
    have heq : (32 * d * F) * (ρ * r) = F * (2 * r) := by
      have he := hradius r
      change 16 * d * (ρ * r) = r at he
      nlinarith [congrArg (fun t : ℝ ↦ 2 * F * t) he]
    refine ⟨a, ha, ?_⟩
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_left hdist hF
    linarith
  have hs := hstep z (ρ * r) K (mul_pos hρ hr) hK A w hw
    (by simpa only [hradius] using fun x hx ↦ hlo x (hc hx))
    (by simpa only [hradius] using fun x hx ↦ hhi x (hc hx))
    (by simpa only [hradius] using fun j x hx ↦ hsource j x (hb hx)) hcoupled
  rw [hradius] at hs
  have herr : 2 * (ρ * r) + K * r ^ 2 ≤ (2 * ρ + K) * r := by
    have hpow : r ^ 2 ≤ r := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hpow hK
    nlinarith
  exact hs.trans (add_le_add le_rfl herr)

end OAI.Analysis.PDE.Elliptic
