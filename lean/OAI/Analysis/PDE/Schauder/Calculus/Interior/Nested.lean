import OAI.Analysis.PDE.Schauder.Calculus.Interior.Localized
import OAI.Analysis.PDE.Schauder.Dirichlet.LocalCutoffSchauder

open Set Metric
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance interiorNestedCutoffMatrixGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance interiorNestedCutoffMatrixSpace : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))

/-- Nested localization: the equation is needed
only where the cutoffs live, and the top-order error uses the larger
cutoff. No bound on the solution outside that larger support is needed. -/
theorem fullspace_nested_cutoff_schauder (hm : 3 ≤ m) (k : Fin m)
    {R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) :
    ∃ P > 0, ∀ (χ : E → ℝ) (_ : ContDiff ℝ 3 χ) (_ : HasCompactSupport χ),
      tsupport χ ⊆ closedBall 0 R →
      ∀ N ε : ℝ, 0 ≤ N → 0 < ε → ∃ D > 0,
      ∀ B : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α,
      P * (m : ℝ) * m * ‖B‖ * (1 + (2 * R + 1) ^ α) ≤ 1 / 2 →
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B‖ ≤ N →
      ∀ η : E → ℝ, ContDiff ℝ 3 η → HasCompactSupport η →
      (∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1) →
      (∀ x, |η x| ≤ 1) →
      ∀ u : E → ℝ, ContDiff ℝ 3 u →
      ∀ (F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) H M, 0 ≤ H → 0 ≤ M →
      (∀ x ∈ tsupport η, |u x| ≤ M) →
      (∀ x, ∀ y,
        ‖fderiv ℝ (fderiv ℝ (fun z => η z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => η z * u z)) y‖ ≤ H * ‖x-y‖ ^ α) →
      (∀ x, χ x ≠ 0 →
        nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
      ∀ x, ∀ y,
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖ ^ α := by
  obtain ⟨P, hP, hlocal⟩ := fullspace_localized_hessian_interpolation hm k hα hα1 hR
  refine ⟨P, hP, ?_⟩
  intro χ hχ hχc hχR N ε hN hε
  obtain ⟨D, hD, hDlocal⟩ := hlocal χ hχ hχc hχR N ε hN hε
  refine ⟨D, hD, ?_⟩
  intro B hsmall hBN η hη hηc hηone hηbound u hu F H M hH hM hbound hh heq
  have hwbound : ∀ x, |η x * u x| ≤ M := by
    intro x
    by_cases hn : η x = 0
    · simpa only [hn, zero_mul, abs_zero] using hM
    · rw [abs_mul]
      exact (mul_le_mul (hηbound x) (hbound x (subset_closure hn))
        (abs_nonneg _) zero_le_one).trans_eq (one_mul M)
  have hweq : ∀ x, χ x ≠ 0 →
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y)
        (fun z => η z * u z) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x := by
    intro x hn
    rw [nested_cutoff_operator hηone _ hn]
    exact heq x hn
  have hout := hDlocal B hsmall hBN (fun z => η z * u z) (hη.mul hu)
    hηc.mul_right F H M hH hM hwbound hh hweq
  simpa only [nested_cutoff_product hηone] using hout

end OAI.Analysis.PDE.Schauder
