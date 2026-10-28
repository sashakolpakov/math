import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Phase
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices

/-! # Filled Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPhase

noncomputable section

/-! The completed filled PEL action has the exact inactive native
symplectic blocks in the retained local phase coordinates. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL.ParameterChoices OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime) (v : Multiplicity.Odd.Sign E)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))

def nativeCrossMatrix (τ : Fin s) : Matrix (Fin 3) (Fin 3) (Padic q) :=
  LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (τ, false)
    (D.pel.reference.imaginaryScalar * Multiplicity.nativeCoefficient E D.pel.reference v) •
      (Multiplicity.nativeMatrix E D.pel.reference).map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (τ, false))

include hq in
theorem nativeCrossMatrix_filled (γ : D.RationalSU) (τ : Fin s) :
    nativeCrossMatrix E D v τ * (FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (τ, true)).val =
      ((FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (τ, false))⁻¹).val.transpose * nativeCrossMatrix E D v τ := by
  by_cases hτ : τ = D.pel.reference.distinguished
  · simp only [FilledPEL.ParameterChoices.nativeFilledBlock, hτ, ite_true, inv_one, Matrix.SpecialLinearGroup.coe_one,
      Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]
  · simp only [FilledPEL.ParameterChoices.nativeFilledBlock, hτ, ite_false]
    have ht := UnitaryCrossMatrix.Intrinsic.unitary_cross_inverseTranspose E D.pel.reference (Padic q)
      (GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (τ, false))
      (D.pel.reference.imaginaryScalar * Multiplicity.nativeCoefficient E D.pel.reference v) γ
    have hc : RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E (Padic q) (GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (τ, false)) =
        GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D.pel (τ, true) := by
      ext x
      exact (RingHom.congr_fun (GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D.pel hq τ false) x).symm
    rw [hc] at ht
    exact ht

theorem nativeFilledPEL_localPhase {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)
    (γ : D.RationalSU) (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he).val *ᵥ
      (fun j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
        ((FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ).val Y) j)) =
    (BlockFamilyMatrices.Local.blockFamilySymplectic c (fun τ => FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (τ, false))).val *ᵥ
      ((FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he).val *ᵥ
        (fun j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j))) := by
  funext z
  cases z with
  | inl p =>
      rw [Phase.nativeCompletedPhase_inl, BlockFamilyMatrices.Local.blockFamilySymplectic_inl]
      simp_rw [Phase.nativeCompletedPhase_inl]
      exact congr_fun (FilledPEL.ParameterChoices.nativeFilledPEL_evaluate E D.pel hg hq γ (p.1, false) Y) p.2
  | inr p =>
      rw [Phase.nativeCompletedPhase_inr, BlockFamilyMatrices.Local.blockFamilySymplectic_inr]
      simp_rw [Phase.nativeCompletedPhase_inr]
      rw [FilledPEL.ParameterChoices.nativeFilledPEL_evaluate E D.pel hg hq γ (p.1, true) Y]
      change (nativeCrossMatrix E D v p.1 *ᵥ
        ((FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (p.1, true)).val *ᵥ
          (fun j => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (p.1, true)) (Y j)))) p.2 =
        (((FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (p.1, false))⁻¹).val.transpose *ᵥ
          (nativeCrossMatrix E D v p.1 *ᵥ
            (fun j => Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (p.1, true)) (Y j)))) p.2
      rw [Matrix.mulVec_mulVec, nativeCrossMatrix_filled E D hq v, Matrix.mulVec_mulVec]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPhase
