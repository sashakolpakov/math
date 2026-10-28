import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic

/-! # Local Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalPhase.TestTransport

noncomputable section

/-! The retained local symplectic coordinates on actual completed
PEL vectors, with their exact momentum and position formulas. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
  [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
  {Place : Type*} [Fintype Place] [DecidableEq Place]
  (σ : Place → E →ₐ[ℚ] K) (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
  (θ : E) (hθ : θ ≠ 0) (hθc : NumberField.IsCMField.complexConj E θ = -θ)
  (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
  (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) = RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm E θ H x y)
  (f : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles →ₐ[ℚ] K) (hf : Continuous f)

include hf

theorem completed_localSymplecticChange (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    (RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E K σ hσ θ hθ hθc H hH hHerm e he).val *ᵥ
      (fun j => f (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j)) =
    RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.splitSymplecticCoordinates E K σ hσ θ hθ H hH
      (fun τ i => TensorEvaluation.TestTransport.tensorEvaluation f τ (Y i)) := by
  have hc := SplitCoordinates.TestTransport.coefficientVectorCoordinates_split E K (Equiv.refl (E →ₐ[ℚ] K)) e f hf Y
  rw [SplitCoordinates.TestTransport.splitLabelCoordinates_refl] at hc
  simp only [Equiv.refl_apply] at hc
  rw [RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange_mulVec, ← hc]
  simp only [RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.rationalToSplitCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem completed_localSymplecticChange_inl (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)
    (τ : Place) (i : Fin 3) :
    ((RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E K σ hσ θ hθ hθc H hH hHerm e he).val *ᵥ
      (fun j => f (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j))) (Sum.inl (τ, i)) =
      TensorEvaluation.TestTransport.tensorEvaluation f (σ τ) (Y i) := by
  rw [completed_localSymplecticChange E K σ hσ θ hθ hθc H hH hHerm e he f hf]
  rfl

theorem completed_localSymplecticChange_inr (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)
    (τ : Place) (i : Fin 3) :
    ((RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.localSymplecticChange E K σ hσ θ hθ hθc H hH hHerm e he).val *ᵥ
      (fun j => f (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j))) (Sum.inr (τ, i)) =
      ((σ τ θ • H.map (σ τ)) *ᵥ
        (fun j => TensorEvaluation.TestTransport.tensorEvaluation f (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K (σ τ)) (Y j))) i := by
  rw [completed_localSymplecticChange E K σ hσ θ hθ hθc H hH hHerm e he f hf]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalPhase.TestTransport
