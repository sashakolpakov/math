import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap
import OAI.RepresentationTheory.Hecke.RadialDilation.FunctionSumMap

/-! # Prime Phase Action -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization

noncomputable section

/-! A local symplectic action changes only the local Heisenberg index. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q n : ℕ) [Fact q.Prime]

def fullPrimeMomentum (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => ((FiniteConjugation.Realization.finitePadicSymplecticInclusion q (SymplecticSwap.Realization.symplecticSwapHom g)).val *ᵥ Sum.elim p s) (Sum.inl i)

def fullPrimePosition (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => ((FiniteConjugation.Realization.finitePadicSymplecticInclusion q (SymplecticSwap.Realization.symplecticSwapHom g)).val *ᵥ Sum.elim p s) (Sum.inr i)

theorem fullPrimeProjection_sum_elim (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeProjection q (Sum.elim p s) =
      Sum.elim (PrimeChart.Realization.fullPrimeProjection q p) (PrimeChart.Realization.fullPrimeProjection q s) :=
  FunctionSumMap.Realization.function_map_sum_elim (FiniteSchur.Realization.finitePadicProjection q) p s

theorem fullPrimeProjection_swap_components (x : Sum (Fin n) (Fin n) → Theta.PoissonAutomorphyNormalizationData.AQf) :
    Sum.elim (PrimeChart.Realization.fullPrimeProjection q (fun i => x (Sum.inr i)))
      (PrimeChart.Realization.fullPrimeProjection q (fun i => x (Sum.inl i))) = SymplecticSwap.Realization.swapPhase (PrimeChart.Realization.fullPrimeProjection q x) := rfl

theorem fullPrimeProjection_swapped_sum (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) :
    SymplecticSwap.Realization.swapPhase (PrimeChart.Realization.fullPrimeProjection q (Sum.elim p s)) =
      Sum.elim (PrimeChart.Realization.fullPrimeProjection q s) (PrimeChart.Realization.fullPrimeProjection q p) :=
  FunctionSumMap.Realization.function_map_swap_sum_elim (FiniteSchur.Realization.finitePadicProjection q) p s

theorem fullPrime_localPhase_components (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) :
    Sum.elim (PrimeChart.Realization.fullPrimeProjection q (fullPrimePosition q n g p s))
      (PrimeChart.Realization.fullPrimeProjection q (fullPrimeMomentum q n g p s)) =
      SymplecticSwap.Realization.swapPhase (PrimeChart.Realization.fullPrimeProjection q
        ((FiniteConjugation.Realization.finitePadicSymplecticInclusion q (SymplecticSwap.Realization.symplecticSwapHom g)).val *ᵥ Sum.elim p s)) :=
  fullPrimeProjection_swap_components q n _

theorem fullPrime_swapped_projection (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (x : Sum (Fin n) (Fin n) → Theta.PoissonAutomorphyNormalizationData.AQf) :
    SymplecticSwap.Realization.swapPhase (PrimeChart.Realization.fullPrimeProjection q ((FiniteConjugation.Realization.finitePadicSymplecticInclusion q (SymplecticSwap.Realization.symplecticSwapHom g)).val *ᵥ x)) =
      g.val *ᵥ SymplecticSwap.Realization.swapPhase (PrimeChart.Realization.fullPrimeProjection q x) := by
  rw [PrimeMatrixAction.Realization.fullPrime_symplectic_projection, SymplecticSwap.Realization.symplecticSwapHom_action, SymplecticSwap.Realization.swapPhase_involutive]

theorem fullPrime_transformed_localPhase (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) :
    Sum.elim (PrimeChart.Realization.fullPrimeProjection q (fullPrimePosition q n g p s))
      (PrimeChart.Realization.fullPrimeProjection q (fullPrimeMomentum q n g p s)) =
      g.val *ᵥ Sum.elim (PrimeChart.Realization.fullPrimeProjection q s) (PrimeChart.Realization.fullPrimeProjection q p) :=
  (fullPrime_localPhase_components q n g p s).trans
    ((fullPrime_swapped_projection q n g (Sum.elim p s)).trans
      (congrArg (fun v => g.val *ᵥ v) (fullPrimeProjection_swapped_sum q n p s)))

theorem fullPrime_transformed_away_momentum (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeAway q (fullPrimeMomentum q n g p s) = PrimeChart.Realization.fullPrimeAway q p := by
  have h := PrimeMatrixAction.Realization.fullPrime_symplectic_away q (SymplecticSwap.Realization.symplecticSwapHom g) (Sum.elim p s)
  apply Subtype.ext
  funext i
  exact congrFun (congrArg Subtype.val h) (Sum.inl i)

theorem fullPrime_transformed_away_position (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : Fin n → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeAway q (fullPrimePosition q n g p s) = PrimeChart.Realization.fullPrimeAway q s := by
  have h := PrimeMatrixAction.Realization.fullPrime_symplectic_away q (SymplecticSwap.Realization.symplecticSwapHom g) (Sum.elim p s)
  apply Subtype.ext
  funext i
  exact congrFun (congrArg Subtype.val h) (Sum.inr i)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PrimePhaseAction.Realization
