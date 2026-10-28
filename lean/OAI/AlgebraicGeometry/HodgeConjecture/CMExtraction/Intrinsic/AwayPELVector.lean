import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPhase
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ActiveResidualProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SymplecticConjugateVector

/-! # Away PEL Vector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELVector

noncomputable section

/-! The actual residual and filled PEL operator agree on all completed
vectors after projection to the chosen prime. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SymplecticConjugateVector.TestTransport

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hμ : D.pel.reference.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

theorem nativeAwayPEL_vector
    (huS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (γ : D.RationalSU) (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom (D.weil.finite.project
      (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ))).val *ᵥ
      (fun j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e Y j)) =
      (fun j => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
        ((FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ).val Y) j)) :=
  SymplecticConjugateVector.TestTransport.symplectic_vector_of_conjugation _ (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he)
    (BlockFamilyMatrices.Local.blockFamilySymplectic c (fun τ => FilledPEL.ParameterChoices.nativeFilledBlock E D.pel γ (τ, false))) _ _
    (ActiveResidualProjection.nativeActiveResidual_projection E D hg hμ v hv e he c u hu
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he) huS γ)
    (FilledPhase.nativeFilledPEL_localPhase E D hg hq v e he c γ Y)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELVector
