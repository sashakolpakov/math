import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteConjugation
import OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPhase

/-! # Finite Scalar Projection -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteScalarProjection.Realization

noncomputable section

/-! The finite conjugate of a rational scalar has the required active local projection. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

theorem symplectic_conjugation_action {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (S G : Theta.PoissonAutomorphyNormalizationData.Sp ι K) (F : (Sum ι ι → K) → (Sum ι ι → K))
    (hF : ∀ x, S.val *ᵥ (G.val *ᵥ x) = F (S.val *ᵥ x)) (x : Sum ι ι → K) :
    (S * G * S⁻¹).val *ᵥ x = F x := by
  have hc : S.val *ᵥ (S⁻¹).val *ᵥ x = x := by
    rw [Matrix.mulVec_mulVec]
    change (S * S⁻¹).val *ᵥ x = x
    rw [mul_inv_cancel]
    exact Matrix.one_mulVec x
  change (S.val * G.val * (S⁻¹).val) *ᵥ x = F x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hF, hc]

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

theorem finite_coordinate_scalar_projection
    (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (s : MpF)
    (hs : D.finite.project s = FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x)) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    (D.finite.project (s * D.finiteLift γ * s⁻¹)).val *ᵥ FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ v =
      FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q (a μ)⁻¹)) v) := by
  apply FinitePhaseProjection.Realization.finiteMatrix_localBlock_action
  intro w
  have hm := congrArg Subtype.val (FiniteConjugation.Realization.finite_coordinate_conjugation_projection q D S s hs γ)
  change (D.finite.project (s * D.finiteLift γ * s⁻¹)).val.map (FiniteSchur.Realization.finitePadicProjection q) =
    (S * Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ * S⁻¹).val at hm
  rw [hm, symplectic_conjugation_action S _ _ hscalar, ScalarPhase.Realization.pairedScalarPhase_localBlock]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteScalarProjection.Realization
