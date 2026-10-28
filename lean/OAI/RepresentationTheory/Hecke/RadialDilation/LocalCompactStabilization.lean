import OAI.RepresentationTheory.Hecke.RadialDilation.LocalWeilSmoothness
import OAI.RepresentationTheory.Hecke.RadialDilation.CompactPowers

/-! # Local Compact Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalCompactStabilization.Realization

noncomputable section

/-! Compact local scalar orbits have positive powers fixing each test vector with finite phase. -/

open scoped Classical _root_.Topology _root_.Matrix
open Filter _root_.Matrix

variable (q n : ℕ) [Fact q.Prime]

instance padicSymplecticFirstCountable : FirstCountableTopology (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n) := by
  let : FirstCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ_[q]) :=
    inferInstanceAs (FirstCountableTopology ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℚ_[q]))
  exact TopologicalSpace.firstCountableTopology_induced _ _ Subtype.val

instance padicSymplecticTopologicalGroup : IsTopologicalGroup (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n × Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n => p.1.val * p.2.val)
    exact ((LocalBigCellStabilization.Realization.padicSymplectic_continuous_val q n).comp continuous_fst).mul
      ((LocalBigCellStabilization.Realization.padicSymplectic_continuous_val q n).comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n => (-Matrix.J (Fin n) ℚ_[q]) * g.val.transpose * Matrix.J (Fin n) ℚ_[q])
    exact (continuous_const.mul (LocalBigCellStabilization.Realization.padicSymplectic_continuous_val q n).matrix_transpose).mul continuous_const

local instance c410LocalCompactStabilization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalCompactStabilization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem exists_local_power_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (C : Set (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n)) (hC : IsCompact C)
    (hg : ∀ N : ℕ, (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g) ^ N ∈ C) :
    ∃ (N : ℕ) (ξ : ℂ), 0 < N ∧ ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N) f = ξ • f := by
  have hnear := LocalWeilSmoothness.Realization.eventually_local_weil_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial f
  obtain ⟨N, hN, hphase⟩ := CompactPowers.Realization.exists_positive_power_mem_nhds
    (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g) C hC hg hnear
  obtain ⟨ξ, hξ, hf⟩ := hphase (g ^ N) ((Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ).map_pow g N)
  exact ⟨N, ξ, hN, hξ, hf⟩

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalCompactStabilization.Realization
