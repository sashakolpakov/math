import OAI.Analysis.PDE.Variational.PeriodizedTests
import OAI.Analysis.PDE.Variational.WeakSolution
import OAI.Analysis.PDE.Weak.Elliptic.TestSupport

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology InnerProductSpace
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem periodic_weak_solution_compact_test (J : Finset (Fin (m+1)))
    (a b : CellCoordinates m) (hL : ∀ i∈J, a i<b i)
    (Ω : Set (CellCoordinates m))
    (hΩ : ∀ (z : J → ℤ) (x : CellCoordinates m),
      x + coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (hu : ∀ ψ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
      (∫ x in Icc a b, inner ℝ (cellGradient ψ x) (A x (u.val x))) =
        ∫ x in Icc a b, f x * ψ.val x)
    (φ : CellCoordinates m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω ∩ cellInterior a b) :
    (∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x))) =
      ∫ x in Icc a b, f x * φ x := by
  have hsΩ : tsupport φ ⊆ Ω := fun x hx ↦ (hs hx).1
  have hsc : tsupport φ ⊆ cellInterior a b := fun x hx ↦ (hs hx).2
  let ψ := periodizedTest J a b hL Ω hΩ φ hφ hc hsΩ
  calc
    _ = ∫ x in Icc a b, inner ℝ (cellGradient ψ x) (A x (u.val x)) := by
      apply integral_congr_ae
      filter_upwards [ae_cellInterior a b] with x hx
      rw [show cellGradient ψ x = cellGradient φ x from
        periodizedTest_gradient_eq J a b hL Ω hΩ φ hφ hc hsΩ hsc hx]
    _ = _ := hu ψ
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change f x * ψ.val x = f x * φ x
      rw [show ψ.val x = φ x from periodizedTest_eq J a b hL Ω hΩ φ hφ hc hsΩ hsc hx]

def coefficientCellFlux (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (u : PeriodicH10 a b Ω P) : CellCoordinates m → CellVectors m :=
  cellZeroExtension a b (OAI.Analysis.PDE.Dirichlet.coefficientLpCLM A hA hM hAM u.val)

theorem memLp_coefficientCellFlux (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (u : PeriodicH10 a b Ω P) : MemLp (coefficientCellFlux a b Ω P A hA hM hAM u) 2 volume :=
  memLp_cellZeroExtension a b _

theorem coefficientCellFlux_ae (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (u : PeriodicH10 a b Ω P) :
    coefficientCellFlux a b Ω P A hA hM hAM u =ᵐ[volume]
      (fun x ↦ A x (cellZeroExtension a b u.val x)) := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp
    (OAI.Analysis.PDE.Dirichlet.coefficientLpCLM_ae A hA hM hAM u.val)
  filter_upwards [h] with x hx
  by_cases hxc : x∈Icc a b
  · simpa only [coefficientCellFlux, cellZeroExtension, indicator_of_mem hxc] using hx hxc
  · simp [coefficientCellFlux, cellZeroExtension, hxc]

theorem integral_coefficientCellFlux (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (u : PeriodicH10 a b Ω P) (w : CellCoordinates m → CellVectors m) :
    (∫ x, inner ℝ (coefficientCellFlux a b Ω P A hA hM hAM u x) (w x)) =
      ∫ x in Icc a b, inner ℝ (A x (u.val x)) (w x) := by
  have hpoint : (fun x ↦ inner ℝ (coefficientCellFlux a b Ω P A hA hM hAM u x) (w x)) =
      (Icc a b).indicator
        (fun x ↦ inner ℝ (OAI.Analysis.PDE.Dirichlet.coefficientLpCLM A hA hM hAM u.val x) (w x)) := by
    funext x
    by_cases hx : x∈Icc a b <;> simp [coefficientCellFlux, cellZeroExtension, hx]
  rw [hpoint, integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [OAI.Analysis.PDE.Dirichlet.coefficientLpCLM_ae A hA hM hAM u.val] with x hx
  rw [hx]

/-- The actual local PDE against arbitrary compactly supported smooth tests. -/
theorem coefficientCellFlux_localEquation (J : Finset (Fin (m+1)))
    (a b : CellCoordinates m) (hL : ∀ i∈J, a i<b i)
    (Ω : Set (CellCoordinates m))
    (hΩ : ∀ (z : J → ℤ) (x : CellCoordinates m),
      x + coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (hu : ∀ ψ : PeriodicTests Ω (coordinatePeriodSet J (b-a)),
      (∫ x in Icc a b, inner ℝ (cellGradient ψ x) (A x (u.val x))) =
        ∫ x in Icc a b, f x * ψ.val x) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω ∩ cellInterior a b)
      (coefficientCellFlux a b Ω (coordinatePeriodSet J (b-a)) A hA hM hAM u)
      (cellZeroExtension a b f) := by
  intro φ hφ hc hs
  rw [integral_coefficientCellFlux]
  calc
    _ = ∫ x in Icc a b, inner ℝ (cellGradient φ x) (A x (u.val x)) := by
      congr 1
      funext x
      exact real_inner_comm _ _
    _ = ∫ x in Icc a b, f x * φ x :=
      periodic_weak_solution_compact_test J a b hL Ω hΩ A f u hu φ hφ hc hs
    _ = _ := by
      simpa only [mul_comm] using (integral_mul_cellZeroExtension a b f φ).symm

/-- Lax–Milgram gives a genuine local weak solution and L² weak gradient, with
zero-Dirichlet and periodic conditions encoded by the completed test space. -/
theorem exists_periodic_local_weak_solution (J : Finset (Fin (m+1)))
    (a b : CellCoordinates m) (hab : a≤b) (hL : ∀ i∈J, a i<b i)
    (Ω : Set (CellCoordinates m))
    (hΩ : ∀ (z : J → ℤ) (x : CellCoordinates m),
      x + coordinatePeriodShift J (b-a) z ∈ Ω → x ∈ Ω)
    (k : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M lam : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (hlam : 0<lam)
    (hell : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ v : CellVectors m,
      lam * ‖v‖^2 ≤ inner ℝ v (A x v))
    (f : Lp ℝ 2 (volume.restrict (Icc a b))) :
    ∃ u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)),
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω ∩ cellInterior a b)
        (coefficientCellFlux a b Ω (coordinatePeriodSet J (b-a)) A hA hM hAM u)
        (cellZeroExtension a b f) ∧
      lam * ‖u‖ ≤ (2 * (b k-a k)) * ‖f‖ := by
  obtain ⟨u, hu, hb⟩ := exists_periodic_weak_solution a b hab Ω
    (coordinatePeriodSet J (b-a)) k hface A hA hM hAM hlam hell f
  exact ⟨u, coefficientCellFlux_localEquation J a b hL Ω hΩ A hA hM hAM f u hu, hb⟩

end OAI.Analysis.PDE.Variational
