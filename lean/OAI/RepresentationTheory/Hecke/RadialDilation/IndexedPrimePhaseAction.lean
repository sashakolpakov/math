import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart
import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPhaseFunctions
import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
import OAI.RepresentationTheory.Hecke.RadialDilation.PrimeMatrixAction

/-! # Indexed Prime Phase Action -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization

noncomputable section

/-! A relabeled local symplectic matrix changes only its local phase coordinates. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} (e : I ≃ Fin n)

def indexedPrimeSymplectic : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q] →* Theta.PoissonAutomorphyNormalizationData.Sp I Theta.PoissonAutomorphyNormalizationData.AQf :=
  (FiniteConjugation.Realization.finitePadicSymplecticInclusion q).comp ((PositionReindex.Realization.symplecticReindex e.symm).comp SymplecticSwap.Realization.symplecticSwapHom)

def indexedPrimeMomentum (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) : I → Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => ((indexedPrimeSymplectic q e g).val *ᵥ Sum.elim p s) (Sum.inl i)

def indexedPrimePosition (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) : I → Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => ((indexedPrimeSymplectic q e g).val *ᵥ Sum.elim p s) (Sum.inr i)

def indexedPhaseProjection (x : Sum I I → Theta.PoissonAutomorphyNormalizationData.AQf) : Sum (Fin n) (Fin n) → ℚ_[q] :=
  PositionReindex.Realization.positionReindex (e.sumCongr e) (PrimeChart.Realization.fullPrimeProjection q x)

omit [Fintype I] [DecidableEq I] in
theorem indexedPhaseProjection_swap_sum (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    SymplecticSwap.Realization.swapPhase (indexedPhaseProjection q e (Sum.elim p s)) =
      Sum.elim (IndexedPrimeChart.Realization.indexedPrimeProjection q e s) (IndexedPrimeChart.Realization.indexedPrimeProjection q e p) :=
  IndexedPhaseFunctions.Realization.function_reindex_map_swap_sum e (FiniteSchur.Realization.finitePadicProjection q) p s

omit [Fintype I] [DecidableEq I] in
theorem indexedPhaseProjection_components (x : Sum I I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    Sum.elim (IndexedPrimeChart.Realization.indexedPrimeProjection q e (fun i => x (Sum.inr i)))
      (IndexedPrimeChart.Realization.indexedPrimeProjection q e (fun i => x (Sum.inl i))) = SymplecticSwap.Realization.swapPhase (indexedPhaseProjection q e x) :=
  IndexedPhaseFunctions.Realization.function_reindex_phase_components e (FiniteSchur.Realization.finitePadicProjection q) x

theorem indexedPrime_swapped_projection (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (x : Sum I I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    SymplecticSwap.Realization.swapPhase (indexedPhaseProjection q e ((indexedPrimeSymplectic q e g).val *ᵥ x)) =
      g.val *ᵥ SymplecticSwap.Realization.swapPhase (indexedPhaseProjection q e x) := by
  change SymplecticSwap.Realization.swapPhase (PositionReindex.Realization.positionReindex (e.sumCongr e) (PrimeChart.Realization.fullPrimeProjection q
    ((FiniteConjugation.Realization.finitePadicSymplecticInclusion q (PositionReindex.Realization.symplecticReindex e.symm (SymplecticSwap.Realization.symplecticSwapHom g))).val *ᵥ x))) = _
  rw [PrimeMatrixAction.Realization.fullPrime_symplectic_projection, PositionReindex.Realization.symplecticReindex_inverse_action, SymplecticSwap.Realization.symplecticSwapHom_action,
    SymplecticSwap.Realization.swapPhase_involutive]
  rfl

theorem indexedPrime_transformed_localPhase (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    Sum.elim (IndexedPrimeChart.Realization.indexedPrimeProjection q e (indexedPrimePosition q e g p s))
      (IndexedPrimeChart.Realization.indexedPrimeProjection q e (indexedPrimeMomentum q e g p s)) =
      g.val *ᵥ Sum.elim (IndexedPrimeChart.Realization.indexedPrimeProjection q e s) (IndexedPrimeChart.Realization.indexedPrimeProjection q e p) :=
  (indexedPhaseProjection_components q e ((indexedPrimeSymplectic q e g).val *ᵥ Sum.elim p s)).trans
    ((indexedPrime_swapped_projection q e g (Sum.elim p s)).trans
      (congrArg (fun v => g.val *ᵥ v) (indexedPhaseProjection_swap_sum q e p s)))

theorem indexedPrime_transformed_away_momentum (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeAway q (indexedPrimeMomentum q e g p s) = PrimeChart.Realization.fullPrimeAway q p := by
  have h := PrimeMatrixAction.Realization.fullPrime_symplectic_away q (PositionReindex.Realization.symplecticReindex e.symm (SymplecticSwap.Realization.symplecticSwapHom g)) (Sum.elim p s)
  apply Subtype.ext
  funext i
  exact congrFun (congrArg Subtype.val h) (Sum.inl i)

theorem indexedPrime_transformed_away_position (g : Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ_[q]) (p s : I → Theta.PoissonAutomorphyNormalizationData.AQf) :
    PrimeChart.Realization.fullPrimeAway q (indexedPrimePosition q e g p s) = PrimeChart.Realization.fullPrimeAway q s := by
  have h := PrimeMatrixAction.Realization.fullPrime_symplectic_away q (PositionReindex.Realization.symplecticReindex e.symm (SymplecticSwap.Realization.symplecticSwapHom g)) (Sum.elim p s)
  apply Subtype.ext
  funext i
  exact congrFun (congrArg Subtype.val h) (Sum.inr i)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization
