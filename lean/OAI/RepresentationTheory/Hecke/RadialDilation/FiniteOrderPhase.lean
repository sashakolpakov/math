import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.RepresentationTheory.Hecke.RadialDilation.SimultaneousFinitePhase

/-! # Finite Order Phase -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteOrderPhase.Realization

noncomputable section

/-! Eigenphases above a finite-order symplectic matrix have bounded finite order. -/

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem finite_cover_eigenphase_order (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (m : MpF) (k : ℕ) (hk : D.finite.project m ^ k = 1)
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (hf : f ≠ 0) (ξ : ℂ)
    (hξ : D.finite.action m f = ξ • f) : ξ ^ (2 * k) = 1 := by
  have hp : D.finite.project (m ^ k) = D.finite.project 1 := by
    rw [map_pow, hk, map_one]
  obtain ⟨ε, hε, ha⟩ := FiniteSchur.Realization.finite_lifts_differ_by_sign D (m ^ k) 1 hp
  have hpow := SimultaneousFinitePhase.Realization.linearAction_pow_eigen D.finite.action m f ξ hξ k
  have heq : ξ ^ k • f = ε • f := by
    rw [← hpow, ha, map_one]
    rfl
  have he : ξ ^ k = ε := (smul_left_injective ℂ hf) heq
  rw [Nat.mul_comm, pow_mul, he, hε]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteOrderPhase.Realization
