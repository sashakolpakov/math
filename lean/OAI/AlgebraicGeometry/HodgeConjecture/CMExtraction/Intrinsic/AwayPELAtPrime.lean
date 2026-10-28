import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELVector
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ActiveResidualProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseBasis
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SymplecticConjugateVector

/-! # Away PEL At Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELAtPrime

noncomputable section

/-! Equality of the actual residual and filled PEL matrices at q. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

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

theorem nativeAwayPEL_at_prime
    (huS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (γ : D.RationalSU) (i j : (Fin s × Fin 3) ⊕ (Fin s × Fin 3)) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q ((D.weil.finite.project
      (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ)).val i j) =
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E D.pel.reference e (FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ) i j) := by
  have hvec := AwayPELVector.nativeAwayPEL_vector E D hg hq hμ v hv e he c u hu huS γ
    (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (e.symm (Pi.single j 1)))
  have hentry := SymplecticConjugateVector.TestTransport.symplectic_projected_column (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom _ _ _ j
    (PEL.PhaseBasis.TestTransport.coefficientVectorCoordinates_basis_projection E e (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom j) hvec i
  exact hentry.trans (congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q)
    (PEL.PhaseBasis.TestTransport.pelPhaseMatrix_column E e D.pel.reference (FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ) i j).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELAtPrime
