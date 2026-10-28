import OAI.Analysis.PDE.Weak.Elliptic.CoefficientExtension
import OAI.Analysis.PDE.Weak.Elliptic.LocalDerivative
import OAI.Analysis.PDE.Variational.LocalizedEquation

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Local coefficients suffice: an outer cutoff extends them elliptically,
while the inner cutoff extracts the actual local weak second derivatives. -/
theorem local_weak_gradient_derivative
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) {lam : ℝ} (hlam : 0 < lam)
    {Ω U V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
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
    ∃ g : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      HasWeakDirectionalDerivativeOn volume V (Pi.single j 1) p.2 g := by
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
  have hηg := hasCompactSupport_cellGradient hηs
  obtain ⟨K, hK⟩ := (hηg.isCompact_range
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp)))).isBounded.exists_norm_le
  have hK' : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K := fun x ↦ hK _ (mem_range_self x)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK' 0)
  have hηd := hηs.fderiv (𝕜 := ℝ)
  obtain ⟨L, hL⟩ := (hηd.isCompact_range
    ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_fderiv one_ne_zero)).isBounded.exists_norm_le
  have hL' : ∀ x, ‖fderiv ℝ η x‖ ≤ L := fun x ↦ hL _ (mem_range_self x)
  obtain ⟨g, _, hg⟩ := interior_weak_gradient_derivative B hB hlam hM0 hD0 hK0 hBM hBD hBe
    p hp f hU hweakB η hη hηs hηM hK' hL' hηsub j
  exact ⟨g, OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivative.cutoff_eq_one volume hη.continuous hηM hηone hg⟩

end OAI.Analysis.PDE.Weak
