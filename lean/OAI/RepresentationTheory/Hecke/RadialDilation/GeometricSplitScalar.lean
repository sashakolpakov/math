import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic
import OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPhase

/-! # Geometric Split Scalar -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar.Realization

noncomputable section

/-! The concrete split coordinates satisfy the matrix input of the rational radial factorization. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

def splitScalarUnits {E K Place : Type*} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K]
    (σ : Place → E →ₐ[ℚ] K) (r : Eˣ) : Place → Kˣ :=
  fun τ => Units.map (σ τ).toMonoidHom r

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
variable (q : ℕ) [Fact q.Prime] [Algebra E ℚ_[q]] [IsScalarTower ℚ E ℚ_[q]]
variable {Place : Type*} [Fintype Place] [DecidableEq Place]

theorem geometric_split_scalar_identity (σ : Place → E →ₐ[ℚ] ℚ_[q])
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E ℚ_[q] σ))
    (θ : E) (hθ : θ ≠ 0) (hθc : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E θ H x y)
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (hγ : γ.val = RationalCoordinates.Realization.rationalScalarMatrix E e (r : E))
    (x : Sum (Place × Fin 3) (Place × Fin 3) → ℚ_[q]) :
    (SplitScalarSymplectic.Realization.localSymplecticChange E ℚ_[q] σ hσ θ hθ hθc H hH hHerm e he).val *ᵥ
      ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
    ScalarPhase.Realization.pairedScalarPhase q (splitScalarUnits σ r)
      ((SplitScalarSymplectic.Realization.localSymplecticChange E ℚ_[q] σ hσ θ hθ hθc H hH hHerm e he).val *ᵥ x) := by
  rw [SplitScalarSymplectic.Realization.localSymplecticChange_mulVec, SplitScalarSymplectic.Realization.localSymplecticChange_mulVec]
  change SplitScalarSymplectic.Realization.rationalToSplitCoordinates E ℚ_[q] σ hσ θ hθ H hH e
    (γ.val.map (algebraMap ℚ ℚ_[q]) *ᵥ x) = _
  rw [hγ]
  exact SplitScalarSymplectic.Realization.rationalToSplitCoordinates_scalar E ℚ_[q] σ hσ θ hθ H hH e r hr x

end

end OAI.RepresentationTheory.Hecke.RadialDilation.GeometricSplitScalar.Realization
