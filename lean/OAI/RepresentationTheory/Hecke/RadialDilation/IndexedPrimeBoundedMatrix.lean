import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimePowerStabilization
import OAI.RepresentationTheory.Hecke.RadialDilation.ReindexedPowerBound
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalSwapTopology

/-! # Indexed Prime Bounded Matrix -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBoundedMatrix.Realization

noncomputable section

/-! Bounded local matrices stabilize actual finite tests with arbitrary finite labels. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] [DecidableEq I]
  {n : ℕ} (e : I ≃ Fin n)
local instance c410IndexedPrimeBoundedMatrix_measurable : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410IndexedPrimeBoundedMatrix_borel : BorelSpace ℚ_[q] := ⟨rfl⟩

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

include e in
theorem exists_indexed_local_bounded_matrix_power_sign
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA) (A : Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) (m : MpF)
    (hm : D.finite.project m = FiniteConjugation.Realization.finitePadicSymplecticInclusion q A)
    (φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (R : ℝ)
    (hA : ∀ (N : ℕ) i j, ‖(A ^ N).val i j‖ ≤ R) :
    ∃ (N : ℕ) (ε : ℂ), 0 < N ∧ ε ^ 2 = 1 ∧ D.finite.action (m ^ N) φ = ε • φ := by
  obtain ⟨_, _, _, _, hsurj, _⟩ := hLocalWeil ℚ_[q] (LocalLiftChoice.Realization.padic_not_discrete q) n hn
    (FiniteSchur.Realization.finiteLocalCharacter q D) (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
    (FiniteSchur.Realization.finiteLocalCharacter_unitary q D) (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D)
  obtain ⟨u, hu⟩ := hsurj (SymplecticSwap.Realization.symplecticSwapHom (PositionReindex.Realization.symplecticReindex e A))
  have hm' : D.finite.project m = IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e
      (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u) := by
    change D.finite.project m = FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (PositionReindex.Realization.symplecticReindex e.symm (SymplecticSwap.Realization.symplecticSwapHom
        (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u)))
    rw [hu, LocalSwapTopology.Realization.symplecticSwapHom_involutive, PositionReindex.Realization.symplecticReindex_symm_apply]
    exact hm
  have huC (N : ℕ) : (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n (FiniteSchur.Realization.finiteLocalCharacter q D) u) ^ N ∈
      LocalBoundedStabilization.Realization.localSymplecticBoundedSet q n R := by
    rw [hu]
    exact ReindexedPowerBound.Realization.reindexed_swapped_power_bound q e A R hA N
  exact IndexedPrimePowerStabilization.Realization.exists_indexedPrime_cover_power_sign q e hLocalWeil hn D u m hm' φ
    (LocalBoundedStabilization.Realization.localSymplecticBoundedSet q n R) (LocalBoundedStabilization.Realization.localSymplecticBoundedSet_isCompact q n R) huC

end

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBoundedMatrix.Realization
