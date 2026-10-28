import OAI.RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace
import OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport

/-! # Split Scalar Symplectic -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization

noncomputable section

section

/-! Simultaneous symplectic coordinates and scalar diagonalization at a completely split place. -/

open scoped Classical TensorProduct _root_.Matrix
open _root_.Matrix

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
variable {Place : Type*} [Fintype Place] [DecidableEq Place]

def splitSymplecticCoordinates (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0) :
    ((E →ₐ[ℚ] K) → Fin 3 → K) ≃ₗ[K] (Sum (Place × Fin 3) (Place × Fin 3) → K) :=
  (SplitPairedTrace.Realization.splitPairedFunctionEquiv E K σ hσ).trans
    (PairedSymplectic.Realization.pairedSymplecticCoordinates (SplitPairedTrace.Realization.splitCrossMatrix E K σ θ H)
      (SplitPairedTrace.Realization.splitCrossMatrix_det_ne_zero E K σ θ hθ H hH))

omit [Algebra E K] [IsScalarTower ℚ E K] [DecidableEq Place] in
theorem splitSymplecticCoordinates_pairing (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (hθc : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (u v : (E →ₐ[ℚ] K) → Fin 3 → K) :
    FramePositivity.Realization.coordinatePairing (splitSymplecticCoordinates E K σ hσ θ hθ H hH u)
      (splitSymplecticCoordinates E K σ hσ θ hθ H hH v) = SplitTrace.Realization.splitTraceBilinear E K θ H u v := by
  unfold splitSymplecticCoordinates
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, PairedSymplectic.Realization.pairedSymplecticCoordinates_pairing,
    SplitPairedTrace.Realization.splitTraceBilinear_paired E K σ hσ θ hθc H hHerm]

theorem splitRationalCoordinates_pairing
    (θ : E) (H : Matrix (Fin 3) (Fin 3) E)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E θ H x y)
    (u v : (E →ₐ[ℚ] K) → Fin 3 → K) :
    FramePositivity.Realization.coordinatePairing (SplitScalarCoordinates.Realization.splitRationalCoordinates E K e u) (SplitScalarCoordinates.Realization.splitRationalCoordinates E K e v) =
      SplitTrace.Realization.splitTraceBilinear E K θ H u v := by
  rw [← PairingTransport.Realization.coordinateBilinear_apply]
  obtain ⟨x, rfl⟩ := (Complexification.Realization.splitRankThreeBaseChange E K).surjective u
  obtain ⟨y, rfl⟩ := (Complexification.Realization.splitRankThreeBaseChange E K).surjective v
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      | tmul b y =>
          rw [SplitScalarCoordinates.Realization.splitRationalCoordinates_tmul, SplitScalarCoordinates.Realization.splitRationalCoordinates_tmul,
            Complexification.Realization.splitRankThreeBaseChange_tmul_eq, Complexification.Realization.splitRankThreeBaseChange_tmul_eq]
          rw [LinearMap.map_smul₂, map_smul, LinearMap.map_smul₂, map_smul]
          rw [PairingTransport.Realization.coordinateBilinear_apply, SplitTrace.Realization.splitTraceBilinear_rational, ← he]
          congr 2
          simp only [FramePositivity.Realization.coordinatePairing, map_sum, map_sub, map_mul]

def rationalToSplitCoordinates (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ)) :
    (Sum (Place × Fin 3) (Place × Fin 3) → K) ≃ₗ[K] (Sum (Place × Fin 3) (Place × Fin 3) → K) :=
  (SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).symm.trans (splitSymplecticCoordinates E K σ hσ θ hθ H hH)

theorem rationalToSplitCoordinates_pairing (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (hθc : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E θ H x y)
    (u v : Sum (Place × Fin 3) (Place × Fin 3) → K) :
    FramePositivity.Realization.coordinatePairing (rationalToSplitCoordinates E K σ hσ θ hθ H hH e u)
      (rationalToSplitCoordinates E K σ hσ θ hθ H hH e v) = FramePositivity.Realization.coordinatePairing u v := by
  unfold rationalToSplitCoordinates
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    splitSymplecticCoordinates_pairing E K σ hσ θ hθ hθc H hH hHerm,
    ← splitRationalCoordinates_pairing E K θ H e he,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end

/-! The concrete local symplectic change puts norm-one multiplication in paired scalar form. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
variable {Place : Type*} [Fintype Place] [DecidableEq Place]

omit [IsGalois ℚ E] [Algebra E K] [IsScalarTower ℚ E K] [Fintype Place] [DecidableEq Place] in
theorem splitSymplecticCoordinates_scalar (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (u : (E →ₐ[ℚ] K) → Fin 3 → K) :
    splitSymplecticCoordinates E K σ hσ θ hθ H hH (SplitScalarCoordinates.Realization.splitScalarEnd E K (r : E) u) =
      Sum.elim
        (fun p => σ p.1 (r : E) * splitSymplecticCoordinates E K σ hσ θ hθ H hH u (Sum.inl p))
        (fun p => (σ p.1 (r : E))⁻¹ * splitSymplecticCoordinates E K σ hσ θ hθ H hH u (Sum.inr p)) := by
  unfold splitSymplecticCoordinates
  rw [LinearEquiv.trans_apply, SplitPairedTrace.Realization.splitPairedFunctionEquiv_scalar E K σ hσ r hr]
  exact PairedSymplectic.Realization.pairedCoordinateEquiv_scalar _ (fun τ => σ τ (r : E)) _

theorem rationalToSplitCoordinates_scalar (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (x : Sum (Place × Fin 3) (Place × Fin 3) → K) :
    rationalToSplitCoordinates E K σ hσ θ hθ H hH e
      ((RationalCoordinates.Realization.rationalScalarMatrix E e (r : E)).map (algebraMap ℚ K) *ᵥ x) =
      Sum.elim
        (fun p => σ p.1 (r : E) * rationalToSplitCoordinates E K σ hσ θ hθ H hH e x (Sum.inl p))
        (fun p => (σ p.1 (r : E))⁻¹ * rationalToSplitCoordinates E K σ hσ θ hθ H hH e x (Sum.inr p)) := by
  obtain ⟨u, rfl⟩ := (SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).surjective x
  rw [← SplitScalarCoordinates.Realization.rational_matrix_realizes_split_scalar E K e (r : E)]
  simp only [rationalToSplitCoordinates, LinearEquiv.trans_apply]
  rw [(SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).symm_apply_apply,
    (SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).symm_apply_apply]
  exact splitSymplecticCoordinates_scalar E K σ hσ θ hθ H hH r hr u

def localSymplecticChange (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (hθc : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E θ H x y) :
    Matrix.symplecticGroup (Place × Fin 3) K := by
  let C := rationalToSplitCoordinates E K σ hσ θ hθ H hH e
  refine ⟨LinearMap.toMatrix' C.toLinearMap, PairingTransport.Realization.preserving_coordinatePairing_symplectic _ ?_⟩
  intro u v
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact rationalToSplitCoordinates_pairing E K σ hσ θ hθ hθc H hH hHerm e he u v

theorem localSymplecticChange_mulVec (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
    (θ : E) (hθ : θ ≠ 0) (hθc : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Place × Fin 3) (Place × Fin 3) → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E θ H x y)
    (u : Sum (Place × Fin 3) (Place × Fin 3) → K) :
    (localSymplecticChange E K σ hσ θ hθ hθc H hH hHerm e he).val *ᵥ u =
      rationalToSplitCoordinates E K σ hσ θ hθ H hH e u :=
  LinearMap.toMatrix'_mulVec _ _

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization
