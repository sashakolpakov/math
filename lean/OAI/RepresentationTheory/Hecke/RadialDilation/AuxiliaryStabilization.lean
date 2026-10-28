import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedAdelicStabilization
import OAI.RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor

/-! # Auxiliary Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryStabilization.Realization

noncomputable section

/-! Bounded auxiliary matrices yield one finite phase on the whole radial input space. -/

open scoped Classical _root_.Matrix
open IsDedekindDomain

theorem matrix_power_fixes_vector {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (g : Theta.PoissonAutomorphyNormalizationData.Sp I K) (x : Sum I I → K) (hx : g.val *ᵥ x = x) (N : ℕ) :
    (g ^ N).val *ᵥ x = x := by
  induction N with
  | zero => exact Matrix.one_mulVec x
  | succ N ih =>
      rw [pow_succ]
      change ((g ^ N).val * g.val) *ᵥ x = x
      rw [← Matrix.mulVec_mulVec, hx, ih]

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem exists_auxiliary_power_uniform_radial_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (g : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) Theta.PoissonAutomorphyNormalizationData.AQf)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (S : Finset (HeightOneSpectrum ℤ))
    (he : ∀ v ∉ S, Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) g =
      Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ))
    (hbounded : ∀ (p : ℕ) [Fact p.Prime], ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection p).toRingHom g) ^ N).val i j‖ ≤ R)
    (hfix : ∀ p s : Mem.Realization.Position q,
      g.val *ᵥ Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) =
        Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s)) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : MpF, D.finite.project m = g ^ N →
      ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : Cm.radialInput q,
        D.finite.action m (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b) =
          ξ • Canonical.Realization.canonicalFiniteRadialEmbedding q μ b := by
  let : Nonempty (Place × Fin 3) := ⟨(μ, 0)⟩
  obtain ⟨N, hN, hphase⟩ := IndexedAdelicStabilization.Realization.exists_indexed_adelic_power_vacuum_phase hLocalWeil Fintype.card_pos
    D g γ S he hbounded
  refine ⟨N, hN, ?_⟩
  intro m hm
  obtain ⟨ξ, hξ, hvac⟩ := hphase m hm
  refine ⟨ξ, hξ, CanonicalVacuumTensor.Realization.auxiliary_vacuum_phase_uniform_radial q μ D m ?_ ξ hvac⟩
  intro p s
  rw [hm]
  exact matrix_power_fixes_vector g _ (hfix p s) N

end

end OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryStabilization.Realization
