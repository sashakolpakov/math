import OAI.Analysis.PDE.Concentration.ActualEnergy
import OAI.Analysis.PDE.Concentration.LocalSupermean

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open Laplacian Set Metric
open scoped ContDiff Matrix.Norms.Elementwise

/-- The actual corrected moving-fiber energy satisfies local probability
supermean. Neither its C² regularity nor its mean inequality is assumed. -/
theorem actualEnergy_local_supermean {d : ℕ} (a : ℝ) (ha : 0 < a)
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
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hball : closedBall z R ⊆ physicalEnergyAnnulus a) :
    weightedBallAverage (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 =>
      OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u y +
        (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime y‖ ^ 2)) z r /
        (∫ y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3, meanWeight y) ≤
      OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u z +
        (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ^ 2) := by
  have hF : ContDiffOn ℝ 2 (OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u)
      (physicalEnergyAnnulus a) :=
    ((OAI.Analysis.PDE.Green.contDiffOn_physicalCombinedEnergy a ha e lam hA hB hu).of_le (by simp)).mono
      (fun y hy => hy.1)
  have hG : ContDiffOn ℝ 2 (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 =>
      OAI.Analysis.PDE.Green.setFiberCombinedEnergy e lam (OAI.Analysis.PDE.Green.physicalEnergyCell d a) A B u y +
        (δ / 4) * (16 - ‖OAI.Analysis.PDE.Green.energyComplexTime y‖ ^ 2)) (physicalEnergyAnnulus a) :=
    hF.add (contDiffOn_const.mul (contDiffOn_const.sub
      ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime 2).norm_sq ℂ).contDiffOn))
  apply normalized_weightedBallAverage_le_of_contDiffOn (isOpen_physicalEnergyAnnulus a)
    hG z hr hrR hball
  intro y hy
  exact (corrected_actualEnergy_superharmonic a ha e lam hA hB hu hδ hweak hnonneg y
    (hball (closedBall_subset_closedBall hrR.le hy))).2

end OAI.Analysis.PDE.Concentration
