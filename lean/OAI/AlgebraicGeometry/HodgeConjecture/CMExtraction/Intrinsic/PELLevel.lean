import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryAwayTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel

/-! # PEL Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PELLevel

noncomputable section

/-! The concrete principal PEL away level on the original native
rational residual group, with its induced unitary topology. -/

open scoped Classical _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel.Approximation

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
  (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (NumberField.maximalRealSubfield E))
  (hN : 0 < D.pel.level)

def nativePELLevel :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu w
    OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu) := by
  let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu w
  exact (AdmissibleAwayLevel.Approximation.chosenCMAwayPELLevel E D.pel.reference hg.reference_admissible w D.pel.level hN).comap
    (UnitaryAwayTopology.nativeUnitaryAwayHom E D hg hμ v hv e he c u hu w)
    (UnitaryAwayTopology.nativeUnitaryAway_continuous E D hg hμ v hv e he c u hu w)

theorem nativePELLevel_rational (γ : D.RationalSU) :
    let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu w
    RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ ∈ nativePELLevel E D hg hμ v hv e he c u hu w hN ↔
      CM.AwayPELLevel.Approximation.cmAwayToPEL E D.pel.reference hg.reference_admissible w
        (CM.FiniteAway.Approximation.cmRationalFiniteAway E D.pel.reference hg.reference_admissible w γ) ∈
        D.pel.reference.adelicPrincipalLevel D.pel.level := by
  let := UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv e he c u hu w
  exact (Iff.of_eq (congrArg
    (fun g : CM.FiniteAway.Approximation.CMFiniteAway E D.pel.reference hg.reference_admissible w =>
      g ∈ AdmissibleAwayLevel.Approximation.chosenCMAwayPELLevel E D.pel.reference hg.reference_admissible w D.pel.level hN)
    (UnitaryAwayTopology.nativeUnitaryAwayHom_rational E D hg hμ v hv e he c u hu w γ))).trans
      (AdmissibleAwayLevel.Approximation.chosenCMAwayPELLevel_mem E D.pel.reference hg.reference_admissible w D.pel.level hN _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PELLevel
