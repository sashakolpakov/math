import OAI.RepresentationTheory.Hecke.Geometric
import OAI.RepresentationTheory.Hecke.Family
import OAI.RepresentationTheory.Hecke.Dilation
import OAI.RepresentationTheory.Hecke.Analytic
import OAI.RepresentationTheory.Hecke.Geometry

/-! # Galois Valuation From -/

namespace OAI.RepresentationTheory.Hecke.GaloisValuationFrom

noncomputable section

/-! Native geometric GaloisValuation with the analytic and Hecke propositions discharged.
The coordinates and finite lift come from SphericalAction's full auxiliary-dilation
construction. The same r, M, omega, phase, canonical theta map, radial
inclusion and character are retained through the signed valuation argument.

The theorem retains the original geometric setup, good splitting, IsogenyQuotient
correspondence realization, finite coordinates, actual away topology and
open level, marked-level compatibility, and dense rational image.
Nonvanishing requires an actual nonzero theta value.
-/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

open OAI.RepresentationTheory.Hecke.Geometric.GaloisValuation
attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem native_galois_valuations_from_geometric_inputs
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hc : D.HasFiniteCoordinates)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar)
    (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) :
    ∃ (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF) (hu : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u),
    ∀ [TopologicalSpace (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
      [IsTopologicalGroup (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
      (L : OpenSubgroup (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)),
      (∀ γ : D.RationalSU, IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ ∈ L ↔
        γ ∈ D.rationalAwayLevel ∧ ∀ w : Fin s × Bool,
          w.1 ≠ D.pel.reference.distinguished → D.localMatrix w γ ∈ Theta.Geometric.SphericalGU.Spherical.integralSL3 q) →
      DenseRange (IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).rationalFinite →
      Geometric.GaloisValuation.GeometricGeometricThetaOutput E (IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L) u ιE v hg hq hIsogenyQuotient := by
  obtain ⟨e, he, u, hu, hfamily⟩ := IntrinsicAuxiliaryDilation.SphericalActionIntrinsic.native_auxiliary_dilation_from_full_RadialDilation
    E Dilation.GaloisValuation.dilation_proved Analytic.GaloisValuation.local_weil_proved Analytic.GaloisValuation.poisson_proved D hg hq hμ ιE v hv
  refine ⟨e, he, u, hu, ?_⟩
  intro _ _ L hL hdense
  let N := IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L
  have hTateComparison := Geometry.GaloisValuation.hecke_action_proved hs hdegree D.pel hg hq hIsogenyQuotient
  have hout := Geometry.GaloisValuation.theta_covariance_proved hs hdegree N hg hq hIsogenyQuotient hTateComparison
    (IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_finiteCoordinates E D hg hμ v hv e he c u hu L hc hL)
    (IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_holomorphic E D hg hμ v hv e he c u hu L)
    (IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_automorphy E D hg hμ v hv e he c u hu L) hdense
  obtain ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov⟩ := hout
  refine ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact Family.GaloisValuation.native_radial_family_with_signs E D hg hμ ιE v hv e he c u hu L j
    (N.totalPeriodMap j X component cover) rhoForms eH Θ hΘ huniq hcov hfamily f hf

end

end OAI.RepresentationTheory.Hecke.GaloisValuationFrom
