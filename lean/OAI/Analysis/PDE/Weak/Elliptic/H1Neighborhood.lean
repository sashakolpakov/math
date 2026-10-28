import OAI.Analysis.PDE.Weak.Elliptic.InteriorH1Derivative
import OAI.Analysis.PDE.Weak.Elliptic.H2Neighborhood

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem local_H1_derivative
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) {lam : ℝ} (hlam : 0 < lam)
    {Ω U V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U) (hUΩ : U ⊆ Ω) (hV : IsOpen V)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hweak : WeakDivergenceEquation Ω (fun x ↦ A x (p.2 x)) f)
    (θ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hθ : ContDiff ℝ ∞ θ) (hθs : HasCompactSupport θ)
    (hθrange : ∀ x, θ x ∈ Icc (0 : ℝ) 1) (hθsub : tsupport θ ⊆ Ω)
    (hθone : ∀ x ∈ U, θ x = 1)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηM : ∀ x, |η x| ≤ 1) (hηsub : tsupport η ⊆ U)
    (hηone : ∀ x ∈ V, η x = 1) (j : Fin (m + 1)) :
    ∃ q : H1Pair m, q ∈ H1Zero univ ∧
      HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.1 q.1 ∧
      HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.2 q.2 := by
  let B := ellipticExtension A θ lam
  have hB : ContDiff ℝ 1 B := contDiff_ellipticExtension hA (hθ.of_le (by simp)) lam
  obtain ⟨M, D, hM0, hD0, hBM, hBD⟩ :=
    ellipticExtension_bounded_C1 hA (hθ.of_le (by simp)) hθs lam
  have hBe : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (B x z) z :=
    ellipticExtension_elliptic hθrange hθsub hell
  have hweakB : WeakDivergenceEquation U
      (fieldMultiplierCLM B hB.continuous.aestronglyMeasurable (Eventually.of_forall hBM) p.2) f := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on hweak hUΩ
    · filter_upwards [fieldMultiplierCLM_ae B hB.continuous.aestronglyMeasurable
        (Eventually.of_forall hBM) p.2] with x hx
      intro hxu
      rw [hx, show B x = A x from ellipticExtension_eq lam (hθone x hxu)]
    · exact Eventually.of_forall fun _ _ ↦ rfl
  obtain ⟨K, hK⟩ := ((hasCompactSupport_cellGradient hηs).isCompact_range
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp)))).isBounded.exists_norm_le
  have hK' : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K := fun x ↦ hK _ (mem_range_self x)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK' 0)
  obtain ⟨L, hL⟩ := ((hηs.fderiv (𝕜 := ℝ)).isCompact_range
    ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_fderiv one_ne_zero)).isBounded.exists_norm_le
  have hL' : ∀ x, ‖fderiv ℝ η x‖ ≤ L := fun x ↦ hL _ (mem_range_self x)
  obtain ⟨q, hq, hq0, hq1⟩ := interior_H1_derivative B hB hlam hM0 hD0 hK0 hBM hBD hBe
    p hp f hU hweakB η hη hηs hηM hK' hL' hηsub j
  have he := OAI.Analysis.PDE.Variational.cutoffH1Pair_eq_on V hV η (hη.of_le (by simp)) hηM hK' hηone p
  refine ⟨q, hq, ?_, ?_⟩
  · apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume hq0.on
    · filter_upwards [he] with x hx
      exact fun hxs ↦ (hx hxs).1
    · exact Eventually.of_forall fun _ _ ↦ rfl
  · apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume hq1.on
    · filter_upwards [he] with x hx
      exact fun hxs ↦ (hx hxs).2
    · exact Eventually.of_forall fun _ _ ↦ rfl

/-- Every first derivative of an actual weak elliptic solution has a
local H¹ representative, with no supplied cutoff or global coefficient bound. -/
theorem interior_H1_derivatives_near_point
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hweak : WeakDivergenceEquation Ω (fun x ↦ A x (p.2 x)) f)
    {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ Ω) :
    ∃ V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∀ j : Fin (m + 1), ∃ q : H1Pair m, q ∈ H1Zero univ ∧
        HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.1 q.1 ∧
        HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.2 q.2 := by
  obtain ⟨θ, U, hU, hxU, hUΩ, hθ, hθs, hθsub, hθrange, hθone⟩ :=
    exists_cutoff_with_open_plateau hΩ hx
  obtain ⟨η, V, hV, hxV, hVU, hη, hηs, hηsub, hηrange, hηone⟩ :=
    exists_cutoff_with_open_plateau hU hxU
  refine ⟨V, hV, hxV, hVU.trans hUΩ, ?_⟩
  intro j
  exact local_H1_derivative A hA hlam hU hUΩ hV hell p hp f hweak
    θ hθ hθs hθrange hθsub hθone η hη hηs
    (fun y ↦ by rw [abs_of_nonneg (hηrange y).1]; exact (hηrange y).2)
    hηsub hηone j

end OAI.Analysis.PDE.Weak
