import OAI.Analysis.PDE.Weak.Elliptic.Coefficient
import OAI.Analysis.PDE.Weak.Elliptic.TestEnergy

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}

omit [NormedSpace ℝ X] in
theorem vectorProductL2_cutoff (η : X → ℝ) (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (g : X → E) (hg : Continuous g) {K : ℝ}
    (hK : ∀ x, ‖g x‖ ≤ K) (u : Lp ℝ 2 μ) :
    vectorProductL2 g hg hK (cutoffL2 η hη hM u) =
      cutoffL2 η hη hM (vectorProductL2 g hg hK u) := by
  apply Lp.ext
  filter_upwards [vectorProductL2_ae g hg hK (cutoffL2 η hη hM u),
    cutoffL2_ae η hη hM u, cutoffL2_ae η hη hM (vectorProductL2 g hg hK u),
    vectorProductL2_ae g hg hK u] with x hx hy hz hw
  rw [hx, hy, hz, hw]
  simp [smul_smul]

variable {m : ℕ}

theorem cutoffH1Pair_twice_gradient (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hη : ContDiff ℝ 1 η) {M K : ℝ}
    (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K) (p : H1Pair m) :
    (cutoffH1Pair η hη hM hK (cutoffH1Pair η hη hM hK p)).2 =
      cutoffL2 η hη.continuous hM
        (cutoffL2 η hη.continuous hM p.2 +
          (2 : ℝ) • vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1) := by
  change cutoffL2 η hη.continuous hM
      (cutoffL2 η hη.continuous hM p.2 +
        vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1) +
      vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK
        (cutoffL2 η hη.continuous hM p.1) = _
  rw [vectorProductL2_cutoff, map_add, map_add, map_smul]
  module

theorem cutoffH1Pair_twice_gradient_norm (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hη : ContDiff ℝ 1 η) {K : ℝ}
    (hM : ∀ x, |η x| ≤ 1) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K) (p : H1Pair m) :
    ‖(cutoffH1Pair η hη hM hK (cutoffH1Pair η hη hM hK p)).2‖ ≤
      ‖cutoffL2 η hη.continuous hM p.2‖ +
        2 * ‖vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1‖ := by
  rw [cutoffH1Pair_twice_gradient]
  calc
    _ ≤ 1 * ‖cutoffL2 η hη.continuous hM p.2 +
        (2 : ℝ) • vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1‖ :=
      norm_cutoffL2_le η hη.continuous hM _
    _ ≤ _ := by
      simpa [norm_smul] using norm_add_le
        (cutoffL2 η hη.continuous hM p.2)
        ((2 : ℝ) • vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient hη) hK p.1)

/-- The squared-cutoff difference test is admissible, and so is its
backward difference, whenever the actual cutoff and its translate fit. -/
theorem H1Zero.cutoff_difference_test {p : H1Pair m} (hp : p ∈ H1Zero univ)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) {M K : ℝ}
    (hM : ∀ x, |η x| ≤ M) (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hsub : tsupport η ⊆ Ω) (hshift : (fun x ↦ x + (-h) • v) ⁻¹' tsupport η ⊆ Ω) :
    let q := cutoffH1Pair η (hη.of_le (by simp)) hM hK
      (cutoffH1Pair η (hη.of_le (by simp)) hM hK (differenceH1Pair v h p))
    q ∈ H1Zero (tsupport η) ∧ differenceH1Pair v (-h) q ∈ H1Zero Ω := by
  dsimp only
  have hd := OAI.Analysis.PDE.Weak.H1Zero.difference hp v h (Subset.rfl) (subset_univ _)
  have hc := OAI.Analysis.PDE.Weak.H1Zero.cutoff hd η hη hM hK (inter_subset_left : tsupport η ∩ univ ⊆ tsupport η)
  have hcc := OAI.Analysis.PDE.Weak.H1Zero.cutoff hc η hη hM hK (inter_subset_left : tsupport η ∩ tsupport η ⊆ tsupport η)
  exact ⟨hcc, OAI.Analysis.PDE.Weak.H1Zero.difference hcc v (-h) hsub hshift⟩

end OAI.Analysis.PDE.Weak
