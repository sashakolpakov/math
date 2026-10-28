import OAI.RepresentationTheory.Hecke.Geometric
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedDilation

/-! # Fixed Geometric -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedGeometric

noncomputable section

/-! Construct the geometric radial family for a specified rational basis and
finite lift. The nonzero test may be chosen before the good prime; the
construction retains its coordinates through the same canonical theta map,
radial inclusion, scalar, phase, character, and signed valuations. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

open OAI.RepresentationTheory.Hecke.Geometric.GaloisValuation
attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_fixed_galois_valuations_from_geometric_inputs
    (hGeometricTheta : RepresentationTheory.Hecke.SphericalAction.GeometricThetaInput) (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hSphericalAction : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.SphericalAction.Proposition.{1})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hc : D.HasFiniteCoordinates)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF) (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (huExact : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he)) :
    ∀ [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
      [IsTopologicalGroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
      (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)),
      (∀ γ : D.RationalSU, RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu γ ∈ L ↔
        γ ∈ D.rationalAwayLevel ∧ ∀ w : Fin s × Bool,
          w.1 ≠ D.pel.reference.distinguished → D.localMatrix w γ ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) →
      DenseRange (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).rationalFinite →
      RepresentationTheory.Hecke.Geometric.GaloisValuation.GeometricGeometricThetaOutput E (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L) u ιE v hg hq hIsogenyQuotient := by
  have hfamily := FixedDilation.native_fixed_dilation_from_full_RadialDilation
    E hRadialDilation hLocalWeil hPoissonAutomorphy D hg hq hμ ιE v hv e he u huExact
  intro _ _ L hL hdense
  let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L
  have hout := hGeometricTheta hs hdegree N hg hq hIsogenyQuotient hTateComparison
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_finiteCoordinates E D hg hμ v hv e he c u hu L hc hL)
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_holomorphic E D hg hμ v hv e he c u hu L)
    (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum_automorphy E D hg hμ v hv e he c u hu L) hdense
  obtain ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov⟩ := hout
  refine ⟨A, hA, eH, eComplex, heComplex, hraw, j, X, component, cover,
    hdim, hcover, hbranches, hprojector, rhoForms, hrho, Θ, hΘ, huniq, hcov, ?_⟩
  intro f hf
  exact RepresentationTheory.Hecke.GeometricFamily.GaloisValuation.native_radial_family_with_signs E D hg hμ ιE v hv e he c u hu L hSphericalAction hRationalStructure j
    (N.totalPeriodMap j X component cover) rhoForms eH Θ hΘ huniq hcov hfamily f hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedGeometric
