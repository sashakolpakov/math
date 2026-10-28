import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELAtPrime
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELOtherPrime
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PadicExt

/-! # Away PEL Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELMatrix

noncomputable section

/-! The actual native away Weil matrix is exactly the original filled
PEL operator in the retained rational phase basis. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PadicExt.TestTransport

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

theorem nativeAwayPEL_matrix
    (huS : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he)) (γ : D.RationalSU) :
    (D.weil.finite.project (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ)).val =
      PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E D.pel.reference e (FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ) := by
  funext i j
  apply Finite.PadicExt.TestTransport.finitePadicProjection_ext
  intro p hp
  by_cases hpq : p = q
  · subst p
    exact AwayPELAtPrime.nativeAwayPEL_at_prime E D hg hq hμ v hv e he c u hu huS γ i j
  · exact AwayPELOtherPrime.nativeAwayPEL_other_prime E D hg hμ v hv e he c u hu γ p hpq i j

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELMatrix
