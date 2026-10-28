import OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeWeil
import OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalPowerBounds

/-! # Active Finite Phase -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase.Realization

noncomputable section

/-! A coordinate-independent active finite matrix, with an eighth-root radial formula for every lift. -/

open scoped Classical _root_.Matrix

theorem activeCoordinateUnits_inv {Place K : Type*} [DecidableEq Place] [Monoid K]
    (μ : Place) (a : Kˣ) :
    (fun i => (DiagonalUnits.Realization.activeCoordinateUnits μ a i)⁻¹) = DiagonalUnits.Realization.activeCoordinateUnits μ a⁻¹ := by
  funext i
  by_cases hi : i.1 = μ <;> simp [DiagonalUnits.Realization.activeCoordinateUnits, hi]

theorem activeCoordinateUnits_pow {Place K : Type*} [DecidableEq Place] [Monoid K]
    (μ : Place) (a : Kˣ) (N : ℕ) :
    (fun i => DiagonalUnits.Realization.activeCoordinateUnits μ a i ^ N) = DiagonalUnits.Realization.activeCoordinateUnits μ (a ^ N) := by
  funext i
  by_cases hi : i.1 = μ <;> simp [DiagonalUnits.Realization.activeCoordinateUnits, hi]

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)

def activeFiniteSymplectic (a : ℚ_[q]ˣ) : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) Theta.PoissonAutomorphyNormalizationData.AQf :=
  FiniteConjugation.Realization.finitePadicSymplecticInclusion q (DiagonalPowerBounds.Realization.diagonalSymplectic (DiagonalUnits.Realization.activeCoordinateUnits μ a⁻¹))

theorem activeFiniteSymplectic_pow (a : ℚ_[q]ˣ) (N : ℕ) :
    activeFiniteSymplectic q μ a ^ N = activeFiniteSymplectic q μ (a ^ N) := by
  unfold activeFiniteSymplectic
  rw [← map_pow, DiagonalPowerBounds.Realization.diagonalSymplectic_pow, activeCoordinateUnits_pow, inv_pow]

theorem indexed_activePrime_projection {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (a : ℚ_[q]ˣ) :
    IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (Weil.Local.Generators.Construction.leviSymplectic (ActivePrimeSubstitution.Realization.activePrimeGL q e μ a)) = activeFiniteSymplectic q μ a := by
  change FiniteConjugation.Realization.finitePadicSymplecticInclusion q (PositionReindex.Realization.symplecticReindex e.symm
    (SymplecticSwap.Realization.symplecticSwapHom (Weil.Local.Generators.Construction.leviSymplectic (DiagonalUnits.Realization.diagonalUnitMatrix
      (fun i => DiagonalUnits.Realization.activeCoordinateUnits μ a (e.symm i)))))) = _
  rw [DiagonalPowerBounds.Realization.reindexed_swapped_diagonal_levi, activeCoordinateUnits_inv]
  rfl

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem every_active_finite_lift_radial_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) (m : MpF)
    (hm : D.finite.project m = activeFiniteSymplectic q μ a) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : Cm.radialInput q,
      D.finite.action m (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b) =
        ξ • Canonical.Realization.canonicalFiniteRadialEmbedding q μ
          (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
  obtain ⟨u, ξ, hu, hξ, hop⟩ := ActivePrimeWeil.Realization.exists_active_prime_lift_radial_substitution q
    (Fintype.equivFin (Place × Fin 3)) μ hLocalWeil D a M ha
  rw [indexed_activePrime_projection] at hu
  obtain ⟨ε, hε, he⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D m u (hm.trans hu.symm)
  refine ⟨ε * ξ, ?_, ?_⟩
  · have hε8 : ε ^ 8 = 1 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
    rw [mul_pow, hε8, hξ, one_mul]
  · intro b
    rw [he, hop, smul_smul]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase.Realization
