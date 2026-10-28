import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayFaithful
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPhaseOther
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SymplecticConjugateVector
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseBasis

/-! # Away PEL Other Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELOtherPrime

noncomputable section

/-! Equality of the residual and filled PEL phase matrices away from q. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

theorem nativeAwayPEL_other_prime (γ : D.RationalSU)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (i j : (Fin s × Fin 3) ⊕ (Fin s × Fin 3)) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p ((D.weil.finite.project
      (RepresentationTheory.Hecke.BlockResidual.SphericalActionIntrinsic.activeResidual E D hg hμ v hv e he c u hu γ)).val i j) =
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E D.pel.reference e (FilledPEL.ParameterChoices.nativeFilledPEL E D.pel hg γ) i j) := by
  have hm := SymplecticConjugateVector.TestTransport.symplectic_map_compare_entries (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
    (algebraMap ℚ (Padic p)) _ _
    (AwayFaithful.activeResidual_other_prime E D hg hμ v hv e he c u hu γ p hpq) i j
  rw [RationalPhaseColumn.Intrinsic.nativeRationalSymplectic_val] at hm
  exact hm.trans (FilledPhaseOther.nativeFilledPhase_other_entry E D.pel hg e γ p hpq i j).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayPELOtherPrime
