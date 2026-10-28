import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.DatumIdentities
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalGeometricTheta
import OAI.RepresentationTheory.Hecke.IntrinsicDatum
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates

/-! # Level Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LevelProjection

noncomputable section

/-! Literal identities for the constructed native datum, kept separate
so subsequent geometric assembly reuses their checked proofs. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

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

variable [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))

local notation "N" => OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L

theorem nativeDatum_local_projection (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    (N).weil.finite.project ((N).splitting (g, 1)) =
      ((N).weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c (N).pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            (N).weil.finite.project u := by
  change D.weil.finite.project (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeSplitting E D hg hμ v hv e he c u hu (g, 1)) = _
  rw [RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeSplitting_local]
  exact CoordinateDualHecke.Local.coordinateDualLift_projection q c D.pel.reference.distinguished D.weil u g

theorem nativeDatum_fixed_projection (hq : D.pel.IsGoodCompletelySplitPrime)
    (hproject : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he)) :
    (N).weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E N hg hq v e he) := by
  rw [DatumIdentities.nativeDatum_coordinate_matrix E D hg hμ v hv e he c u hu L hq]
  exact hproject

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LevelProjection
