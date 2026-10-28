import OAI.Analysis.Calculus.SmoothExtension.HalfspaceSeries
import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Local
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! A genuine smooth extension, with a single function valid at all orders. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.Calculus.FiniteExtension OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem exists_compact_finite_halfspace_extension {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) (f : E → F)
    (hf : ContDiffOn ℝ N f {x | 0 ≤ ℓ x}) (hc : HasCompactSupport f) :
    ∃ g : E → F, ContDiff ℝ N g ∧ HasCompactSupport g ∧ EqOn g f {x | 0 ≤ ℓ x} := by
  obtain ⟨g,hg,heq⟩ := OAI.Analysis.Calculus.FiniteExtension.exists_contDiff_extension_of_contDiffOn_halfspace ℓ ν hν f hf
  obtain ⟨R,hR,hbound⟩ := hc.isBounded.exists_pos_norm_le
  let θ : ContDiffBump (0:E) := ⟨R,R+1,hR,by linarith⟩
  refine ⟨fun x => θ x • g x, θ.contDiff.smul hg, θ.hasCompactSupport.smul_right, ?_⟩
  intro x hx
  dsimp only
  rw [heq hx]
  by_cases hfx : f x = 0
  · simp [hfx]
  · rw [θ.one_of_mem_closedBall]
    · simp
    · change dist x 0 ≤ R
      rw [dist_zero_right]
      exact hbound x (subset_tsupport _ (Function.mem_support.mpr hfx))

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem seeleyExtension_congr_on_halfspace (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    (f g : E → F) (heq : EqOn f g {x | 0 ≤ ℓ x}) :
    OAI.Analysis.PDE.Schauder.levelGlue ℓ f (seeleyReflection ℓ ν f) = OAI.Analysis.PDE.Schauder.levelGlue ℓ g (seeleyReflection ℓ ν g) := by
  funext x
  by_cases hx : 0 ≤ ℓ x
  · simp only [OAI.Analysis.PDE.Schauder.levelGlue,ite_eq_left hx,heq hx]
  · simp only [OAI.Analysis.PDE.Schauder.levelGlue,ite_eq_right hx,seeleyReflection]
    apply tsum_congr
    intro i
    rw [heq]
    rw [Set.mem_ofPred_eq,OAI.Analysis.Calculus.FiniteExtension.reflectionLinear_normal ℓ ν hν]
    exact mul_nonneg_of_nonpos_of_nonpos ((seeleyNode_le_neg_one i).trans (by norm_num))
      (le_of_not_ge hx)

omit [FiniteDimensional ℝ E] in
/-- One and the same Seeley extension is smooth to all orders.  The hypotheses
provide actual finite-order compact extensions, not a pre-assumed smooth one. -/
theorem seeleyExtension_contDiff_infty_of_finite_extensions
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) (f : E → F)
    (hf : ∀ N : ℕ, ∃ g : E → F,
      ContDiff ℝ N g ∧ HasCompactSupport g ∧ EqOn g f {x | 0 ≤ ℓ x}) :
    ContDiff ℝ ∞ (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (seeleyReflection ℓ ν f)) := by
  rw [contDiff_infty]
  intro N
  obtain ⟨g,hg,hgc,hgf⟩ := hf N
  rw [seeleyExtension_congr_on_halfspace ℓ ν hν f g hgf.symm]
  exact seeleyExtension_contDiff_of_compact ℓ ν hg hgc

theorem exists_smooth_compact_data_halfspace_extension
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) (f : E → F)
    (hf : ContDiffOn ℝ ∞ f {x | 0 ≤ ℓ x}) (hc : HasCompactSupport f) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ EqOn g f {x | 0 ≤ ℓ x} := by
  refine ⟨OAI.Analysis.PDE.Schauder.levelGlue ℓ f (seeleyReflection ℓ ν f), ?_, ?_⟩
  · apply seeleyExtension_contDiff_infty_of_finite_extensions ℓ ν hν f
    intro N
    exact exists_compact_finite_halfspace_extension ℓ ν hν f
      (hf.of_le (by exact_mod_cast (show (N:ℕ∞) ≤ ⊤ from le_top))) hc
  · intro x hx
    exact ite_eq_left hx

/-- A single globally C∞ function agrees with the given one-sided smooth
function on a fixed smaller half-ball.  The neighborhood is independent of
the derivative order. -/
theorem exists_smooth_extension_of_halfball
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) (f : E → F)
    (R : ℝ) (hR : 0 < R)
    (hf : ContDiffOn ℝ ∞ f (ball 0 R ∩ {x | 0 ≤ ℓ x})) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧
      EqOn g f (ball 0 (R/4) ∩ {x | 0 ≤ ℓ x}) := by
  let η : ContDiffBump (0:E) := ⟨R/4,R/2,by positivity,by linarith⟩
  have hs : tsupport (η : E → ℝ) ⊆ ball 0 R := by
    rw [η.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [η]; linarith)
  have hlocal : ContDiffOn ℝ ∞ (fun x => η x • f x) {x | 0 ≤ ℓ x} := by
    rw [contDiffOn_infty]
    intro N
    have hfn : ContDiffOn ℝ N f ({x | 0 ≤ ℓ x} ∩ ball 0 R) := by
      simpa only [inter_comm] using
        (hf.of_le (show (N:ℕ∞ω) ≤ ∞ by exact_mod_cast (show (N:ℕ∞) ≤ ⊤ from le_top)))
    exact OAI.Analysis.Calculus.FiniteExtension.contDiffOn_cutoff_smul isOpen_ball f hfn (η : E → ℝ) η.contDiff hs
  obtain ⟨g,hg,heq⟩ := exists_smooth_compact_data_halfspace_extension ℓ ν hν
    (fun x => η x • f x) hlocal η.hasCompactSupport.smul_right
  refine ⟨g,hg,?_⟩
  intro x hx
  rw [heq hx.2]
  dsimp only
  rw [η.one_of_mem_closedBall (ball_subset_closedBall hx.1),one_smul]

end OAI.Analysis.Calculus.SmoothExtension
