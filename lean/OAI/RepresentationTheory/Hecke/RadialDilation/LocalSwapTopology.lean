import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalBigCellStabilization

/-! # Local Swap Topology -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalSwapTopology.Realization

noncomputable section

/-! The coordinate convention change preserves compactness of local matrix powers. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

theorem symplecticSwapHom_involutive {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (g : Theta.PoissonAutomorphyNormalizationData.Sp ι K) : SymplecticSwap.Realization.symplecticSwapHom (SymplecticSwap.Realization.symplecticSwapHom g) = g := by
  apply Subtype.ext
  change Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * Theta.PoissonAutomorphyNormalizationData.coordinateSwap = g.val
  have h : Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * Theta.PoissonAutomorphyNormalizationData.coordinateSwap =
      (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * g.val * (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) := by
    noncomm_ring
  rw [h, SymplecticSwap.Realization.coordinateSwap_square, Matrix.one_mul, Matrix.mul_one]

theorem padicSymplecticSwap_continuous (q n : ℕ) [Fact q.Prime] :
    Continuous (SymplecticSwap.Realization.symplecticSwapHom : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q] → Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q] => Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap)
  exact (continuous_const.mul (LocalBigCellStabilization.Realization.padicSymplectic_continuous_val q n)).mul continuous_const

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalSwapTopology.Realization
