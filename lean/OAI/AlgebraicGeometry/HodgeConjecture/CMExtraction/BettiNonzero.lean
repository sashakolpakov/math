import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaTestNonzero
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroClass

/-! # Betti Nonzero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BettiNonzero.Intrinsic

noncomputable section

/-! The normalized retained test gives a nonzero actual Betti theta class
on the same projective component and canonical period uniformization. -/

open scoped Classical _root_.Matrix
open _root_.CategoryTheory

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem nativeThetaTest_betti_ne_zero
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
    (hu : Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
    (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))
    (T : Intrinsic.NonzeroTest.NativeThetaTest E D.pel.reference hg.reference_admissible hμ v hv e he)
    (hf : T.test ∈ (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).sphericalInputs)
    (i : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).componentComplex i)
    (cover : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).domain → X.analyticSpace)
    (hcover : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).IsPeriodUniformization X cover)
    (Θ : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).IsCanonicalThetaLift hg i
      ((RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).totalPeriodMap i X component cover) Θ) :
    Intrinsic.ThetaClass.nativeThetaClass (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L) hg Θ ⟨T.test, hf⟩ ≠ 0 := by
  let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L
  let z := Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E D.pel.reference hg.reference_admissible
  have hz : z.val ∈ N.domain := by
    change z.val ∈ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b) : Set (Fin 2 → ℂ))
    rw [← Intrinsic.PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]
    exact z.property
  apply Intrinsic.NonzeroClass.nativeThetaClass_ne_zero_of_period_value N hg Θ i X component cover hcover hΘ
    ⟨T.test, hf⟩ ⟨z.val, hz⟩ (Pi.single 0 1)
  change N.thetaUniversal T.test z.val (Pi.single 0 1) ≠ 0
  have hvalue : N.thetaUniversal T.test z.val (Pi.single 0 1) = 1 := T.value
  rw [hvalue]
  exact one_ne_zero

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BettiNonzero.Intrinsic
