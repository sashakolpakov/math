import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaObservedNonzero
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest

/-! # Theta Test Nonzero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaTestNonzero

noncomputable section

/-! The normalized value of the retained native test forces its canonical algebraic theta lift to be nonzero. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest.Multiplicity

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

theorem nativeThetaTest_lift_ne_zero
    (T : NonzeroTest.NativeThetaTest E D.pel.reference hg.reference_admissible hμ v hv e he)
    (hf : T.test ∈ (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).sphericalInputs)
    (j : Fin D.pel.componentCount)
    (m : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).domain →
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L).IsCanonicalThetaLift hg j m Θ) :
    Θ ⟨T.test, hf⟩ ≠ 0 := by
  let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L
  let z := PeriodDomain.Multiplicity.nativeOrigin E D.pel.reference hg.reference_admissible
  have hz : z.val ∈ N.domain := by
    change z.val ∈ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b) : Set (Fin 2 → ℂ))
    rw [← PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]
    exact z.property
  apply ThetaObservedNonzero.Intrinsic.canonicalTheta_lift_ne_zero N hg j m Θ hΘ ⟨T.test, hf⟩ ⟨z.val, hz⟩
  intro hzero
  have hvalue := T.value
  change (N.thetaUniversal T.test z.val) (Pi.single 0 1) = 1 at hvalue
  rw [hzero] at hvalue
  exact zero_ne_one hvalue

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaTestNonzero
