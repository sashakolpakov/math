import OAI.RepresentationTheory.Hecke.RadialDilation.LocalBoundedStabilization
import OAI.RepresentationTheory.Hecke.RadialDilation.SimultaneousFinitePhase

/-! # Local Finite Family Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalFiniteFamilyStabilization.Realization

noncomputable section

/-! A positive power fixes a finite family of local test vectors exactly. -/

open scoped Classical

variable (q n : ℕ) [Fact q.Prime]
local instance c410LocalFiniteFamilyStabilization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalFiniteFamilyStabilization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem exists_local_power_fixes_finite_family
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ) {I : Type*} [Fintype I] (f : I → Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (C : Set (Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n)) (hC : IsCompact C)
    (hg : ∀ N : ℕ, (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g) ^ N ∈ C) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (g ^ N) (f i) = f i := by
  let ρ := Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ
  have hlocal (i : I) : ∃ (m : ℕ) (ξ : ℂ),
      0 < m ∧ ξ ^ 8 = 1 ∧ ρ (g ^ m) (f i) = ξ • f i :=
    LocalCompactStabilization.Realization.exists_local_power_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial g (f i) C hC hg
  obtain ⟨N, ξ, hN, hξ⟩ := SimultaneousFinitePhase.Realization.common_positive_power_finite_phase
    (fun _ : I => ρ) (fun _ : I => g) f hlocal
  refine ⟨N * 8, Nat.mul_pos hN (by decide), ?_⟩
  intro i
  have h := SimultaneousFinitePhase.Realization.linearAction_pow_eigen ρ (g ^ N) (f i) (ξ i) (hξ i).2 8
  rw [← pow_mul, (hξ i).1, one_smul] at h
  exact h

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalFiniteFamilyStabilization.Realization
