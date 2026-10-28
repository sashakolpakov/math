import OAI.Analysis.PDE.Green.LocalExtension
import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Sum

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Metric OAI.Analysis.PDE.Variational OAI.Analysis.Calculus.SmoothExtension OAI.Analysis.PDE.Green
open scoped Topology ContDiff Manifold

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup T]

/-- A compact subset of a smooth open patch admits a compactly supported
cutoff equal to one on a neighborhood, with the product extending smoothly
even when the original function is not smooth outside the patch. -/
theorem exists_compact_localizing_weight {C U : Set E} (hC : IsCompact C)
    (hU : IsOpen U) (hCU : C ⊆ U) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ x, 0 ≤ ρ x) ∧ (∀ x ∈ C, ρ =ᶠ[𝓝 x] (fun _ => 1)) ∧
      ContDiff ℝ ∞ (fun x => ρ x * u x) := by
  obtain ⟨χ, hχ, hχrange, hχone, hχzero⟩ :=
    OAI.Analysis.PDE.Green.exists_smooth_cutoff_near_compact hC hU hCU (k := ⊤)
  obtain ⟨R, hR, hCR⟩ := hC.isBounded.exists_pos_norm_le
  have hsub : C ⊆ interior (closedBall (0 : E) (R + 1)) := by
    intro x hx
    apply isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall
    simp only [mem_ball, dist_zero_right]
    linarith [hCR x hx]
  obtain ⟨β, hβone, hβzero, hβrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, E)) hC.isClosed hsub
      (n := (⊤ : ℕ∞))
  have hβ : ContDiff ℝ ∞ β := contMDiff_iff_contDiff.mp β.contMDiff
  have hβc : HasCompactSupport β :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (R + 1)) hβzero
  refine ⟨fun x => χ x * β x, hχ.mul hβ, hβc.mul_left,
    fun x => mul_nonneg (hχrange x).1 (hβrange x).1, ?_, ?_⟩
  · intro x hx
    filter_upwards [hχone x hx, hβone.filter_mono (nhds_le_nhdsSet hx)] with y hy hz
    rw [hy, hz, one_mul]
  · have hf := OAI.Analysis.PDE.Green.contDiff_cutoff_smul hU hχ hχzero hu
    simpa only [smul_eq_mul, mul_right_comm] using hf.mul hβ

/-- Local smoothness near a compact set of representatives gives a genuine
global periodic extension near all its lattice translates. This constructs
an extension only near the selected compact set; no behavior across a
degenerating parameter boundary is assumed. -/
theorem exists_periodic_extension_near_compact
    (L : T →+ E) (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {C U : Set E} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U)
    (u : E → ℝ) (hu : ContDiffOn ℝ ∞ u U)
    (huper : ∀ x z, u (x + L z) = u x) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ x z, g (x + L z) = g x) ∧
      ∀ x, (∃ z, x + L z ∈ C) → g =ᶠ[𝓝 x] u := by
  obtain ⟨ρ, hρ, hρc, hρ0, hρone, hρu⟩ := exists_compact_localizing_weight hC hU hCU hu
  let D := OAI.Analysis.PDE.Variational.discretePeriodization L ρ
  let B := OAI.Analysis.PDE.Variational.discretePeriodization L (fun x => ρ x * u x)
  have hDc : ContDiff ℝ ∞ D := OAI.Analysis.PDE.Variational.contDiff_discretePeriodization L hL hρ hρc
  have hBc : ContDiff ℝ ∞ B := OAI.Analysis.PDE.Variational.contDiff_discretePeriodization L hL hρu hρc.mul_right
  have hB (x : E) : B x = D x * u x := by
    calc
      B x = ∑' z, ρ (x + L z) * u x := by
        apply tsum_congr
        intro z
        exact congrArg (fun t : ℝ => ρ (x + L z) * t) (huper x z)
      _ = D x * u x := by rw [tsum_mul_right]; rfl
  refine ⟨fun x => OAI.Analysis.Calculus.SmoothExtension.smoothReciprocal (D x) * B x,
    (OAI.Analysis.Calculus.SmoothExtension.contDiff_smoothReciprocal.comp hDc).mul hBc, ?_, ?_⟩
  · intro x z
    simp only [D, B, OAI.Analysis.PDE.Variational.discretePeriodization_add]
  · rintro x ⟨z, hz⟩
    have he : (fun y => ρ (y + L z)) =ᶠ[𝓝 x] (fun _ => 1) :=
      (hρone _ hz).comp_tendsto (continuous_id.add continuous_const).continuousAt
    filter_upwards [he] with y hy
    have hD1 : 1 ≤ D y := by
      rw [← hy]
      exact (OAI.Analysis.Calculus.SmoothExtension.summable_discrete_translates L hL hρc y).le_tsum z (fun j _ => hρ0 _)
    rw [hB, ← mul_assoc, OAI.Analysis.Calculus.SmoothExtension.smoothReciprocal_mul hD1, one_mul]

end OAI.Analysis.PDE.Concentration
