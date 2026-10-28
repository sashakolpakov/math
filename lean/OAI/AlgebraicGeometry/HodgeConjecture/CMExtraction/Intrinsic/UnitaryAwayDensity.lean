import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.InducedAwayDensity

/-! # Unitary Away Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayDensity

noncomputable section

/-! Strong approximation for the actual native rational active/away map,
using the place selected by its original q-adic field embedding. -/

open scoped Classical _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.InducedAwayDensity.Approximation

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

def nativeUnitaryActivePlace : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (NumberField.maximalRealSubfield E) :=
  CM.ActivePlace.Approximation.cmActivePlace E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false))

theorem nativeUnitaryAway_rational_compatible
    [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
    (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)) (γ : D.RationalSU) :
    Prod.map id (UnitaryAwayTopology.nativeUnitaryAwayHom E D hg hμ v hv e he c u hu (nativeUnitaryActivePlace E D))
      ((RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).rationalFinite γ) =
      CM.AdelicBinaryClosure.Approximation.cmActiveAwayRational E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false))
        D.pel.reference.b hg.reference_admissible.2.1 hg.reference_admissible.2.2.1
        D.pel.reference.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E D.pel.reference hg.reference_admissible)
        (OneTheta.Multiplicity.nativeOneDeltaNonzero E D.pel.reference hg.reference_admissible) γ := by
  apply Prod.ext
  · change LocalSymplectic.nativeLocalUnitaryBlocks E D γ D.pel.reference.distinguished = _
    exact (CM.AdelicBinaryClosure.Approximation.cmActiveAwayRational_first E
      (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false))
      D.pel.reference.b hg.reference_admissible.2.1 hg.reference_admissible.2.2.1
      D.pel.reference.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E D.pel.reference hg.reference_admissible)
      (OneTheta.Multiplicity.nativeOneDeltaNonzero E D.pel.reference hg.reference_admissible) γ).symm
  · change UnitaryAwayTopology.nativeUnitaryAwayHom E D hg hμ v hv e he c u hu (nativeUnitaryActivePlace E D)
      (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ) = _
    exact UnitaryAwayTopology.nativeUnitaryAwayHom_rational E D hg hμ v hv e he c u hu (nativeUnitaryActivePlace E D) γ

theorem native_unitary_away_density :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (nativeUnitaryActivePlace E D)
    ∀ L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu),
      DenseRange (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).rationalFinite := by
  let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu (nativeUnitaryActivePlace E D)
  let := UnitaryAwayTopology.nativeUnitaryAway_topologicalGroup E D hg hμ v hv e he c u hu (nativeUnitaryActivePlace E D)
  dsimp only
  intro L
  apply CM.InducedAwayDensity.Approximation.cm_induced_away_density E
    (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false))
    D.pel.reference.b hg.reference_admissible.2.1 hg.reference_admissible.2.2.1
    D.pel.reference.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E D.pel.reference hg.reference_admissible)
    (OneTheta.Multiplicity.nativeOneDeltaNonzero E D.pel.reference hg.reference_admissible)
    (Representatives.Multiplicity.nativePlaces E D.pel.reference hg.reference_admissible hμ)
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).rationalFinite
    (UnitaryAwayTopology.nativeUnitaryAwayHom E D hg hμ v hv e he c u hu (nativeUnitaryActivePlace E D))
  · exact IntrinsicOne.Multiplicity.native_single_ball_negative E D.pel.reference hg.reference_admissible hμ
  · exact ⟨rfl⟩
  · exact nativeUnitaryAway_rational_compatible E D hg hμ v hv e he c u hu L
  · exact (AwayRationalEquiv.nativeAwayRationalEquiv E D hg hμ v hv e he c u hu).surjective

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayDensity
