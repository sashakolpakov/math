import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPhaseColumn

/-! # Rational Unitary Faithful -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalUnitaryFaithful.Intrinsic

noncomputable section

/-! The rational symplectic representation in a specified basis is
faithful, and remains faithful after embedding the rational coefficients
in any field. -/

open scoped Classical _root_.Matrix

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem mapSp_injective {I R S : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (ι := I) f) := by
  intro A B h
  apply Subtype.ext
  ext i j
  exact hf (congrArg (fun M : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S => M.val i j) h)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (v : Multiplicity.Odd.Sign E)
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))

theorem nativeRationalSymplectic_injective :
    Function.Injective (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he) := by
  intro g h hgh
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hm := congrArg (fun M : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ => M.val *ᵥ e (Pi.single j 1)) hgh
  rw [RationalPhaseColumn.Intrinsic.nativeRationalSymplectic_apply, RationalPhaseColumn.Intrinsic.nativeRationalSymplectic_apply] at hm
  have hx := congrFun (e.injective hm) i
  simpa [Matrix.mulVec_single] using hx

theorem nativeRationalSymplectic_local_injective
    {L : Type*} [Field L] (ρ : ℚ →+* L) :
    Function.Injective ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp ρ).comp (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he)) :=
  (mapSp_injective ρ ρ.injective).comp (nativeRationalSymplectic_injective E P e v he)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalUnitaryFaithful.Intrinsic
