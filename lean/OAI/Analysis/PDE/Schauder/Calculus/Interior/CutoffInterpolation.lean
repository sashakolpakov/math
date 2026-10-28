import OAI.Analysis.PDE.Schauder.Calculus.Interior.JetHolder
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformCutoff

open Set
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance interiorCutoffInterpFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance interiorCutoffInterpFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance interiorCutoffInterpMatrixGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance interiorCutoffInterpMatrixSpace : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))

/-- The lower-order cutoff errors are infinitesimal relative to the top
Hölder seminorm. The constant is uniform over a bounded set of coefficients,
and the lower-jet extensions are constructed from the actual solution. -/
theorem fullspace_cutoff_forcing_interpolation (k : Fin m)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : E → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    {N ε : ℝ} (hN : 0 ≤ N) (hε : 0 < ε) :
    ∃ D > 0, ∀ (u : E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, |u x| ≤ M) →
      (∀ x, ∀ y,
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖ ^ α) →
      ∀ (A : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α), ‖A‖ ≤ N →
      ∀ F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α,
      ∃ (U : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (V : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x) ∧
        ‖cutoffJetForcing hα.le hα1 A χ hχ hχc F U V‖ ≤
          ε * H + D * (‖F‖ + M) := by
  obtain ⟨C, hC, hforce⟩ := cutoffJetForcing_uniform_bound hα.le hα1 χ hχ hχc
  let δ := ε / (2 * C * (N + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, hext⟩ := fullspace_lower_jet_holder k hα hα1 hδ
  let D := C + 2 * C * N * B + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hscale : 2 * C * (N + 1) * δ = ε := by
    dsimp [δ]
    field_simp
  have hsmall : 2 * C * N * δ ≤ ε := by
    have ht := mul_le_mul_of_nonneg_left (show N ≤ N + 1 by linarith)
      (show 0 ≤ 2 * C * δ by positivity)
    nlinarith only [ht, hscale]
  refine ⟨D, hD, ?_⟩
  intro u hu huc H M hH hM hbound hh A hA F
  obtain ⟨U, V, hU, hV, hUn, hVn⟩ := hext u hu huc H M hH hM hbound hh
  refine ⟨U, V, hU, hV, ?_⟩
  have hsum : ‖U‖ + ‖V‖ ≤ 2 * (δ * H + B * M) := by linarith
  have hnonneg : 0 ≤ 2 * (δ * H + B * M) := by positivity
  have hproduct : ‖A‖ * (‖U‖ + ‖V‖) ≤ N * (2 * (δ * H + B * M)) :=
    mul_le_mul hA hsum (by positivity) hN
  have hbase := (hforce A F U V).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖F‖) hproduct) hC.le)
  have hsmallH := mul_le_mul_of_nonneg_right hsmall hH
  have hCF : C * ‖F‖ ≤ D * ‖F‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
    dsimp [D]
    have ht : 0 ≤ 2 * C * N * B := by positivity
    linarith
  have hBM : (2 * C * N * B) * M ≤ D * M := by
    apply mul_le_mul_of_nonneg_right _ hM
    dsimp [D]
    linarith
  nlinarith only [hbase, hsmallH, hCF, hBM]

end OAI.Analysis.PDE.Schauder
