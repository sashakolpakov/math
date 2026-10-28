import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection

/-! # Block Fixed Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockFixedPhase.CM

noncomputable section

/-! A simultaneous unitary block matrix whose active block is the
identity fixes the actual finite active phase vectors. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (c : (Place × Fin 3) ≃ Fin n) (μ : Place)

theorem local_fixed (g : Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hg : g μ = 1)
    (w : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c g).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.localBlockPhase q μ w = RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.localBlockPhase q μ w := by
  funext i
  cases i with
  | inl p =>
    rw [CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inl]
    by_cases h : p.1 = μ
    · simp [RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, h, hg]
    · simp only [RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, Sum.elim_inl, ite_eq_right h]
      exact congrFun (Matrix.mulVec_zero _) p.2
  | inr p =>
    rw [CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inr]
    by_cases h : p.1 = μ
    · simp [RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, h, hg]
    · simp only [RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.localBlockPhase, Sum.elim_inr, ite_eq_right h]
      exact congrFun (Matrix.mulVec_zero _) p.2

theorem finite_fixed (A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (g : Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (hg : g μ = 1)
    (hA : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom A = CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c g)
    (p t : Fin 3 → ℚ_[q]) :
    A.val *ᵥ Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ t) =
      Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ t) := by
  change _ *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (Sum.elim t p) = RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (Sum.elim t p)
  apply RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.finiteMatrix_localBlock_action q μ _ id
  intro w
  exact (congrArg (fun M => M *ᵥ RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization.localBlockPhase q μ w) (congrArg Subtype.val hA)).trans
    (local_fixed q c μ g hg w)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockFixedPhase.CM
