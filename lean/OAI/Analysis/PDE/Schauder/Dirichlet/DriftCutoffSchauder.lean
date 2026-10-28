import OAI.Analysis.PDE.Schauder.Dirichlet.NestedCutoffSchauder
import OAI.Analysis.Normed.Function.Holder.Banach.Operator

open Set Metric
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance driftCutoffMatrixGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance driftCutoffMatrixSpace : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))

/-- The nested boundary estimate absorbs a uniformly bounded Hölder drift.
The constant is chosen before the drift and solution, and no derivatives
of the drift are required. This is the first-order term created by a
nonlinear boundary chart. -/
theorem halfspace_nested_cutoff_schauder_with_drift (hm : 3 ≤ m) (k : Fin m)
    {R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) :
    ∃ P > 0, ∀ (χ : E → ℝ) (_ : ContDiff ℝ 3 χ) (_ : HasCompactSupport χ),
      tsupport χ ⊆ closedBall 0 R →
      ∀ N Nb ε : ℝ, 0 ≤ N → 0 ≤ Nb → 0 < ε → ∃ D > 0,
      ∀ B : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α,
      P * (m : ℝ) * m * ‖B‖ * (1 + (2 * R + 1) ^ α) ≤ 1 / 2 →
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B‖ ≤ N →
      ∀ b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α, ‖b‖ ≤ Nb →
      ∀ η : E → ℝ, ContDiff ℝ 3 η → HasCompactSupport η →
      (∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1) →
      (∀ x, 0 ≤ x k → |η x| ≤ 1) →
      ∀ u : E → ℝ, ContDiff ℝ 3 u →
      (∀ x, x k = 0 → η x ≠ 0 → u x = 0) →
      ∀ (F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) H M, 0 ≤ H → 0 ≤ M →
      (∀ x ∈ tsupport η, 0 ≤ x k → |u x| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z => η z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => η z * u z)) y‖ ≤ H * ‖x-y‖ ^ α) →
      (∀ x, 0 ≤ x k → χ x ≠ 0 →
        nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x =
          OAI.Analysis.Normed.Function.Holder.HolderMap.value F x + fderiv ℝ u x (OAI.Analysis.Normed.Function.Holder.HolderMap.value b x)) →
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖ ^ α := by
  obtain ⟨P, hP, hlocal⟩ := halfspace_nested_cutoff_schauder hm k hα hα1 hR
  refine ⟨P, hP, ?_⟩
  intro χ hχ hχc hχR N Nb ε hN hNb hε
  obtain ⟨D₀, hD₀, hestimate⟩ := hlocal χ hχ hχc hχR N (ε / 2) hN (by positivity)
  let δ := ε / (2 * D₀ * (2 * Nb + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨K, hK, hinterp⟩ := halfspace_lower_jet_holder_extensions k hα hα1.le hδ
  let D := D₀ * (2 * Nb * K + 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDge : D₀ ≤ D := by
    dsimp only [D]
    nlinarith [mul_nonneg hNb hK.le]
  have hscaled : D₀ * (2 * Nb) * δ ≤ ε / 2 := by
    calc
      _ ≤ D₀ * (2 * Nb + 1) * δ := by gcongr; linarith
      _ = ε / 2 := by
        dsimp only [δ]
        field_simp

  refine ⟨D, hD, ?_⟩
  intro B hsmall hBN b hbn η hη hηc hηone hηbound u hu hz F H M hH hM hbound hh heq
  have hwbound : ∀ x, 0 ≤ x k → |η x * u x| ≤ M := by
    intro x hx
    by_cases hn : η x = 0
    · simpa only [hn, zero_mul, abs_zero] using hM
    · rw [abs_mul]
      exact (mul_le_mul (hηbound x hx) (hbound x (subset_closure hn) hx)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul M)
  obtain ⟨U, V, _, hV, _, hVnorm⟩ := hinterp (fun z => η z * u z)
    ((hη.mul hu).of_le (by norm_num)) hηc.mul_right H M hH hM hwbound hh
  let F' := F + OAI.Analysis.Normed.Function.Holder.HolderMap.action hα.le V b
  have hF' : ‖F'‖ ≤ ‖F‖ + 2 * Nb * (δ * H + K * M) := by
    calc
      _ ≤ ‖F‖ + ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα.le V b‖ := norm_add_le _ _
      _ ≤ ‖F‖ + 2 * ‖V‖ * ‖b‖ :=
        add_le_add (le_refl ‖F‖) (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα.le V b)
      _ ≤ ‖F‖ + 2 * (δ * H + K * M) * Nb := by gcongr
      _ = _ := by ring
  have hF'eq : ∀ x, 0 ≤ x k → χ x ≠ 0 →
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F' x := by
    intro x hx hn
    change _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x + OAI.Analysis.Normed.Function.Holder.HolderMap.value V x (OAI.Analysis.Normed.Function.Holder.HolderMap.value b x)
    rw [hV x hx, (nested_cutoff_germ (u := u) hηone hn).fderiv_eq (𝕜 := ℝ)]
    exact heq x hx hn
  have hout := hestimate B hsmall hBN η hη hηc hηone hηbound u hu hz
    F' H M hH hM hbound hh hF'eq
  have hbudget : ε / 2 * H + D₀ * (‖F'‖ + M) ≤ ε * H + D * (‖F‖ + M) := by
    calc
      _ ≤ ε / 2 * H + D₀ * (‖F‖ + 2 * Nb * (δ * H + K * M) + M) := by gcongr
      _ = (ε / 2 + D₀ * (2 * Nb) * δ) * H + D₀ * ‖F‖ + D * M := by
        dsimp only [D]
        ring
      _ ≤ ε * H + D * ‖F‖ + D * M := by gcongr; linarith
      _ = _ := by ring
  intro x hx y hy
  exact (hout x hx y hy).trans
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
