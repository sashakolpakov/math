import OAI.Analysis.PDE.Green.ActualSmooth
import OAI.Analysis.PDE.Concentration.CorrectedEnergy

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open Laplacian Set
open scoped ContDiff Matrix.Norms.Elementwise

def physicalEnergyAnnulus (a : ℝ) : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :=
  {z | a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ < 4}

theorem isOpen_physicalEnergyAnnulus (a : ℝ) : IsOpen (physicalEnergyAnnulus a) := by
  have hc := (OAI.Analysis.PDE.Green.contDiff_energyComplexTime 0).continuous.norm
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

theorem energyComplexTime_norm_sq (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2 = (z (0, 1)) ^ 2 + (z (0, 2)) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [OAI.Analysis.PDE.Green.energyComplexTime, Complex.normSq_apply, pow_two]

/-- Weak propagation of the actual moving-fiber energy implies its classical
Laplacian bound. Smoothness of that energy is derived from the data, not
postulated as an additional energy-function hypothesis. -/
theorem actualEnergy_laplacian_le {d : ℕ} (a : ℝ) (ha : 0 < a)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ)}
    (hA : ContDiff ℝ ∞ A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) {δ : ℝ}
    (hweak : ∀ η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ physicalEnergyAnnulus a → (∀ z, 0 ≤ η z) →
      (∫ z, Δ η z * OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u z) ≤
        δ * ∫ z, η z)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ physicalEnergyAnnulus a) :
    Δ (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u) z ≤ δ := by
  have hF : ContDiffOn ℝ 2 (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u)
      (physicalEnergyAnnulus a) :=
    ((OAI.Analysis.PDE.Green.contDiffOn_physicalCombinedEnergy a ha e lam hA hB hu).of_le (by simp)).mono
      (fun z hz => hz.1)
  exact laplacian_le_of_weak_inequality_on (isOpen_physicalEnergyAnnulus a) hF hweak z hz

/-- The explicit correction from the source produces a genuine nonnegative
classical superharmonic function from the actual energy and its weak bound. -/
theorem corrected_actualEnergy_superharmonic {d : ℕ} (a : ℝ) (ha : 0 < a)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ)}
    (hA : ContDiff ℝ ∞ A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) {δ : ℝ} (hδ : 0 ≤ δ)
    (hweak : ∀ η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ physicalEnergyAnnulus a → (∀ z, 0 ≤ η z) →
      (∫ z, Δ η z * OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u z) ≤
        δ * ∫ z, η z)
    (hnonneg : ∀ z ∈ physicalEnergyAnnulus a,
      0 ≤ OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u z)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ physicalEnergyAnnulus a) :
    0 ≤ OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u z +
      (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2) ∧
    Δ ((fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 =>
      OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u y +
      (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime y‖ ^ 2)) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ) z ≤ 0 := by
  have hF : ContDiffOn ℝ 2 (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u)
      (physicalEnergyAnnulus a) :=
    ((OAI.Analysis.PDE.Green.contDiffOn_physicalCombinedEnergy a ha e lam hA hB hu).of_le (by simp)).mono
      (fun z hz => hz.1)
  have he (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
      16 - ‖OAI.Analysis.PDE.Green.energyComplexTime y‖ ^ 2 = coordinateCylinderCorrection (0, 1) (0, 2) y := by
    rw [energyComplexTime_norm_sq]
    unfold coordinateCylinderCorrection
    ring
  simp_rw [he]
  apply corrected_energy_of_weak_bound (0, 1) (0, 2) (isOpen_physicalEnergyAnnulus a)
    hF hδ hweak hz (hnonneg z hz)
  rw [← energyComplexTime_norm_sq]
  have hn := norm_nonneg (OAI.Analysis.PDE.Green.energyComplexTime z)
  have ht := hz.2
  nlinarith

end OAI.Analysis.PDE.Concentration
