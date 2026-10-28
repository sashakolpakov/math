import OAI.Analysis.PDE.Concentration.SpatialCellL2
import OAI.Analysis.PDE.Concentration.DensityBounds

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current _root_.MeasureTheory
open scoped ContDiff

theorem packetCycleFrequency_basis {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (κ : ℝ) (v : Fin d → ℝ)
    (m : Option (Fin d) → ℤ)
    (hm : ∀ i, inner ℝ (packetSpatialFrequency κ v) (R (EuclideanSpace.single i 1)) =
      (m i : ℝ) * (2 * Real.pi) / 100) (i : Option (Fin d)) :
    inner ℝ (packetCycleFrequency κ v) (R (EuclideanSpace.single i 1)) = (m i : ℝ) / 100 := by
  rw [packetCycleFrequency, inner_smul_left, hm]
  simp only [starRingEnd_apply, star_trivial]
  field_simp

theorem integral_sq_packetBaseWave {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hinj : Function.Injective m)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) :
    (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v x y‖ ^ 2) =
      |LinearMap.det (spatialCellMap R).toLinearMap| * ∑ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ^ 2 := by
  unfold packetBaseWave
  rw [integral_sq_physicalSpatialCell R _ m hinj _
    (fun j => packetCycleFrequency_basis R (κ j) (v j) (m j) (hm j))]
  simp only [OAI.Analysis.Calculus.Current.phaseComplex_norm]

/-- The input L² estimate for the actual packet multiplier on the physical
spatial cell. It loses no logarithmic derivatives. -/
theorem packetGaussianField_L2 {d : ℕ} (j : Fin 2)
    {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {χ : TransverseSpace d → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L : ℝ), 0 < h → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ),
      Function.Injective m →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m k i : ℝ) * (2 * Real.pi) / 100) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ), ‖transverseRatio z‖ ≤ w₀ →
      (∫ y in physicalSpatialCell R, ‖packetGaussianField j ρ χ h L κ cR cI v x z y‖ ^ 2) ≤
        (C * (h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) ^ 2 *
          ∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v x y‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := gaussianForwardSymbol_sup j hρ hcρ hχ hcχ hpos w₀
  refine ⟨C, hC, ?_⟩
  intro R h L hh hL ι _ κ cR cI v m hinj hm x z hW
  apply physicalSpatialCell_multiplier_L2 R _ m hinj _ _
    (fun k => packetCycleFrequency_basis R (κ k) (v k) (m k) (hm k))
  intro k
  exact hc (transverseRatio z) hW h hh L hL _

end OAI.Analysis.PDE.Concentration
