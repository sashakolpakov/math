import OAI.Analysis.PDE.Variational.CoordinateLattice

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem isOpen_cellInterior (a b : CellCoordinates m) : IsOpen (cellInterior a b) := by
  change IsOpen {x : CellCoordinates m | ∀ i, a i < x i ∧ x i < b i}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_apply i) continuous_const)

theorem cellInterior_subset_Icc (a b : CellCoordinates m) : cellInterior a b ⊆ Icc a b := by
  intro x hx
  exact ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2.le⟩

theorem ae_cellInterior (a b : CellCoordinates m) :
    ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ cellInterior a b := by
  have h : cellInterior a b =ᵐ[volume] Icc a b := by
    simpa only [cellInterior, Set.pi, Set.mem_univ, forall_const, volume_pi, Set.mem_Ioo] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin (m+1) ↦ (volume : Measure ℝ))
        (f := a) (g := b))
  rw [Measure.restrict_congr_set h.symm]
  exact ae_restrict_mem (isOpen_cellInterior a b).measurableSet

/-- Smooth periodization of a compactly supported interior test, as a genuine member
of the periodic zero-Dirichlet test space. -/
def periodizedTest (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m))
    (hΩ : ∀ (z : J → ℤ) (x : CellCoordinates m),
      x + coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (φ : CellCoordinates m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) : PeriodicTests Ω (coordinatePeriodSet J (b-a)) := by
  refine ⟨discretePeriodization (coordinatePeriodShift J (b-a)) φ, ?_, ?_, ?_⟩
  · exact contDiff_discretePeriodization _
      (finite_coordinatePeriodShift_norm J (b-a) (fun i hi ↦ sub_pos.mpr (hL i hi))) hφ hc
  · intro x hx
    have hzero (z : J → ℤ) : φ (x + coordinatePeriodShift J (b-a) z) = 0 := by
      by_contra hne
      exact hx (hΩ z x (hs (subset_tsupport _ hne)))
    change (∑' z, φ (x + coordinatePeriodShift J (b-a) z)) = 0
    simp only [hzero, tsum_zero]
  · rintro p ⟨z, rfl⟩ x
    exact discretePeriodization_add _ _ z x

theorem periodizedTest_eq (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m))
    (hΩ : ∀ (z : J → ℤ) (x : CellCoordinates m),
      x + coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (φ : CellCoordinates m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) (hcell : tsupport φ ⊆ cellInterior a b)
    {x : CellCoordinates m} (hx : x∈Icc a b) :
    (periodizedTest J a b hL Ω hΩ φ hφ hc hs).val x = φ x :=
  coordinatePeriodization_eq J a b hL hcell hx

theorem periodizedTest_gradient_eq (J : Finset (Fin (m+1))) (a b : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m))
    (hΩ : ∀ (z : J → ℤ) (x : CellCoordinates m),
      x + coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (φ : CellCoordinates m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) (hcell : tsupport φ ⊆ cellInterior a b)
    {x : CellCoordinates m} (hx : x∈cellInterior a b) :
    cellGradient (periodizedTest J a b hL Ω hΩ φ hφ hc hs) x = cellGradient φ x := by
  have heq : (periodizedTest J a b hL Ω hΩ φ hφ hc hs : CellCoordinates m → ℝ) =ᶠ[𝓝 x] φ := by
    filter_upwards [(isOpen_cellInterior a b).mem_nhds hx] with y hy
    exact periodizedTest_eq J a b hL Ω hΩ φ hφ hc hs hcell (cellInterior_subset_Icc a b hy)
  ext i
  simp only [cellGradient_apply, heq.fderiv_eq]

end OAI.Analysis.PDE.Variational
