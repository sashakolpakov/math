import OAI.Analysis.Calculus.Current.Coordinates
import OAI.Analysis.Calculus.Current.Fiber.Normal
import OAI.Analysis.Calculus.Quaternion.Cutoff

/-! The exact cutoff factor in the regularized wave current. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise ContDiff

theorem currentDirection_snd {d : ℕ} (p : Index d × Fin 3) :
    (currentDirection p).2 = OAI.Analysis.Calculus.Quaternion.imaginaryDirection p.1 p.2 := by
  obtain ⟨a, α⟩ := p
  fin_cases α <;> simp [currentDirection, OAI.Analysis.Calculus.Quaternion.imaginaryDirection, OAI.Analysis.Calculus.Quaternion.imaginarySlot]
  funext i
  simp [Pi.single_apply]

theorem currentGradient_snd {d : ℕ} {g : (Index d → ℂ) → ℝ}
    {x : Index d → ℝ} {z : Index d → ℂ} (hg : DifferentiableAt ℝ g z) :
    OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun p => fderiv ℝ (fun q : CurrentSpace d => g q.2) (x, z) (currentDirection p)) =
      OAI.Analysis.Calculus.Quaternion.imaginaryGradient g z := by
  have hF : fderiv ℝ (fun q : CurrentSpace d => g q.2) (x, z) =
      (fderiv ℝ g z).comp (ContinuousLinearMap.snd ℝ (Index d → ℝ) (Index d → ℂ)) := by
    simpa only using! (hg.hasFDerivAt.comp (x, z)
      (ContinuousLinearMap.snd ℝ (Index d → ℝ) (Index d → ℂ)).hasFDerivAt).fderiv
  funext a
  simp only [OAI.Analysis.Calculus.Quaternion.gradientMap, OAI.Analysis.Calculus.Quaternion.imaginaryGradient, hF, ContinuousLinearMap.comp_apply]
  change (∑ α, fderiv ℝ g z ((currentDirection (a, α)).2) • OAI.Analysis.Calculus.Quaternion.threeSlots α) = _
  simp only [currentDirection_snd]

theorem current_smul_divergence_zero {d : ℕ}
    {g : (Index d → ℂ) → ℝ}
    {A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q}
    {x : Index d → ℝ} {z : Index d → ℂ}
    (hg : DifferentiableAt ℝ g z)
    (hA : DifferentiableAt ℝ (fun p : CurrentSpace d => A p.1 p.2) (x, z))
    (hG : star (OAI.Analysis.Calculus.Quaternion.imaginaryGradient g z) ᵥ* A x z = 0)
    (hdiv : ∀ b, OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (threeSlotMatrixDerivative A x z) b = 0)
    (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
      (threeSlotMatrixDerivative (fun q w => g w • A q w) x z) b = 0 := by
  have hg' : DifferentiableAt ℝ (fun p : CurrentSpace d => g p.2) (x, z) :=
    hg.comp (x, z) differentiableAt_snd
  have hweighted : DifferentiableAt ℝ
      (fun p : CurrentSpace d => g p.2 • A p.1 p.2) (x, z) := hg'.smul hA
  have hG' : star (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.threeSlots
      (fun p => fderiv ℝ (fun q : CurrentSpace d => g q.2) (x, z) (currentDirection p)))
        ᵥ* A x z = 0 := by
    rw [currentGradient_snd hg]
    exact hG
  have h := OAI.Analysis.Calculus.Quaternion.strongDivergence_current_smul_zero OAI.Analysis.Calculus.Quaternion.threeSlots currentDirection hg' hA hG'
    (fun j => by simpa only [fderiv_currentDirection hA] using hdiv j) b
  simpa only [fderiv_currentDirection (A := fun q w => g w • A q w) hweighted] using h

def cutoffCurrent {d : ℕ} (g : ℂ → ℝ) (a : ℝ)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (x : Index d → ℝ) (z : Index d → ℂ) : Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q :=
  g (phi z / (a : ℂ)) • A x z

theorem cutoffCurrent_divergence_zero {d : ℕ} (g : ℂ → ℝ) (a : ℝ)
    {A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q}
    {x : Index d → ℝ} {z : Index d → ℂ} (hY : z none ≠ 0)
    (hg : DifferentiableAt ℝ g (phi z / (a : ℂ)))
    (hA : DifferentiableAt ℝ (fun p : CurrentSpace d => A p.1 p.2) (x, z))
    (htan : ∀ b, ∑ c, complexK (phaseRow (ratio z) c) * A x z c b = 0)
    (hdiv : ∀ b, OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (threeSlotMatrixDerivative A x z) b = 0)
    (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (threeSlotMatrixDerivative (cutoffCurrent g a A) x z) b = 0 := by
  have hφ : DifferentiableAt ℂ (phi : (Index d → ℂ) → ℂ) z := by
    unfold phi
    fun_prop (disch := exact mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hY)
  have hscale : DifferentiableAt ℝ (fun q : ℂ => q / (a : ℂ)) (phi z) := by fun_prop
  have hgscale : DifferentiableAt ℝ (fun q : ℂ => g (q / (a : ℂ))) (phi z) :=
    hg.comp (phi z) hscale
  apply current_smul_divergence_zero (hgscale.comp z (hφ.restrictScalars ℝ)) hA
    _ hdiv b
  apply OAI.Analysis.Calculus.Quaternion.imaginaryGradient_real_comp_annihilates hφ hgscale
  simpa only [fderiv_phi_single z hY] using htan

theorem cutoffWaveCurrent_divergence_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (g : ℂ → ℝ) (a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hg : DifferentiableAt ℝ g (phi z / (a : ℂ))) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
      (threeSlotMatrixDerivative (cutoffCurrent g a (waveCurrent κ cR cI v)) x z) b = 0 := by
  apply cutoffCurrent_divergence_zero g a hY hg
  · apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (contDiffAt_waveCurrent κ cR cI v x z hY i j).differentiableAt (by simp)
  · intro j
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using
      waveCurrent_image_tangent κ cR cI v x z (Pi.single j 1)
  · exact waveCurrent_strongDivergence κ cR cI v x z hY

theorem cutoffCurrent_zero_of_outside {d : ℕ} (g : ℂ → ℝ) (a R : ℝ)
    (hg : ∀ q : ℂ, R ≤ ‖q‖ → g q = 0)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (x : Index d → ℝ) (z : Index d → ℂ) (hz : R ≤ ‖phi z / (a : ℂ)‖) :
    cutoffCurrent g a A x z = 0 := by
  simp [cutoffCurrent, hg _ hz]

theorem cutoffCurrent_eq_of_inside {d : ℕ} (g : ℂ → ℝ) (a r : ℝ)
    (hg : ∀ q : ℂ, ‖q‖ ≤ r → g q = 1)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (x : Index d → ℝ) (z : Index d → ℂ) (hz : ‖phi z / (a : ℂ)‖ ≤ r) :
    cutoffCurrent g a A x z = A x z := by
  simp [cutoffCurrent, hg _ hz]

/-- A concrete smooth cutoff with the exact inner and outer radii in the source. -/
def phaseBump : ContDiffBump (0 : ℂ) where
  rIn := 1 / 100
  rOut := 1 / 20
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def phaseCutoff : ℂ → ℝ := phaseBump

theorem phaseCutoff_contDiff : ContDiff ℝ ∞ phaseCutoff := phaseBump.contDiff

theorem phaseCutoff_nonneg (q : ℂ) : 0 ≤ phaseCutoff q := phaseBump.nonneg

theorem phaseCutoff_le_one (q : ℂ) : phaseCutoff q ≤ 1 := phaseBump.le_one

theorem phaseCutoff_eq_one (q : ℂ) (hq : ‖q‖ ≤ 1 / 100) : phaseCutoff q = 1 := by
  apply phaseBump.one_of_mem_closedBall
  simpa [phaseBump, Metric.mem_closedBall, dist_zero_right] using hq

theorem phaseCutoff_eq_zero (q : ℂ) (hq : 1 / 20 ≤ ‖q‖) : phaseCutoff q = 0 := by
  apply phaseBump.zero_of_le_dist
  simpa [phaseBump, dist_zero_right] using hq

theorem cutoffCurrent_isHermitian {d : ℕ} (g : ℂ → ℝ) (a : ℝ)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (x : Index d → ℝ) (z : Index d → ℂ) (hA : (A x z).IsHermitian) :
    (cutoffCurrent g a A x z).IsHermitian := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.conjTranspose_apply, cutoffCurrent, Matrix.smul_apply, Quaternion.star_smul]
  rw [hA.apply]

theorem cutoffCurrent_image_tangent {d : ℕ} (g : ℂ → ℝ) (a : ℝ)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (x : Index d → ℝ) (z : Index d → ℂ)
    (hA : ∀ v, ∑ b, complexK (phaseRow (ratio z) b) * (A x z *ᵥ v) b = 0)
    (v : Index d → OAI.Analysis.Calculus.Quaternion.Q) :
    ∑ b, complexK (phaseRow (ratio z) b) * (cutoffCurrent g a A x z *ᵥ v) b = 0 := by
  simp only [cutoffCurrent, Matrix.smul_mulVec, Pi.smul_apply, mul_smul_comm,
    ← Finset.smul_sum, hA, smul_zero]

theorem cutoffCurrent_quadratic_nonneg {d : ℕ} (g : ℂ → ℝ) (a : ℝ)
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q)
    (x : Index d → ℝ) (z : Index d → ℂ) (hg : 0 ≤ g (phi z / (a : ℂ)))
    (hA : ∀ v, 0 ≤ (∑ b, star (v b) * (A x z *ᵥ v) b).re) (v : Index d → OAI.Analysis.Calculus.Quaternion.Q) :
    0 ≤ (∑ b, star (v b) * (cutoffCurrent g a A x z *ᵥ v) b).re := by
  simp only [cutoffCurrent, Matrix.smul_mulVec, Pi.smul_apply, mul_smul_comm,
    ← Finset.smul_sum, Quaternion.re_smul, smul_eq_mul]
  exact mul_nonneg hg (hA v)

end OAI.Analysis.Calculus.Current
