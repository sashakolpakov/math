import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaScalar

/-! # Family Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta

noncomputable section

section

/-! RadialDilation's pointwise realization uses the constructed native period
family, and its determinant phase is constant over the connected ball. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar *
        Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ) (hγ : γ.val = RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r : E))

include hPoissonAutomorphy hr hγ in
theorem native_theta_scalar_for_period
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ D.pel.reference.domain}) :
    RepresentationTheory.Hecke.RadialDilation.GeometricSpecs.Realization.ThetaScalarRealization (Place := Fin s) (MpR := MpR) (MpF := MpF) (MpA := MpA)
      D.weil γ D.pel.reference.distinguished (Multiplicity.Period.nativeCompactSigns E D.pel.reference v)
      (fun i => D.pel.reference.embeddings i (r : E))
      (Multiplicity.Period.nativeUpperFrame E D.pel.reference hg.reference_admissible v e z)
      (Multiplicity.Period.nativeLowerFrame E D.pel.reference hg.reference_admissible v e z)
      (PeriodFamily.Multiplicity.nativePeriod E D.pel.reference hg.reference_admissible hμ v hv e he z) := by
  obtain ⟨Z, hZ⟩ := ThetaScalar.native_theta_scalar_realization hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z z.property
  have heq := PeriodFamily.Multiplicity.nativePeriod_unique E D.pel.reference hg.reference_admissible hμ v hv e he z Z hZ.1
  exact heq ▸ hZ

include hPoissonAutomorphy hr hγ in
theorem native_halfDet_constant
    (z₀ z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ D.pel.reference.domain}) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (PeriodFamily.Multiplicity.nativePeriod E D.pel.reference hg.reference_admissible hμ v hv e he z) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (PeriodFamily.Multiplicity.nativePeriod E D.pel.reference hg.reference_admissible hμ v hv e he z₀) := by
  let P := D.pel.reference
  let f := fun x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} =>
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (PeriodFamily.Multiplicity.nativePeriod E P hg.reference_admissible hμ v hv e he x)
  let : ConnectedSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} :=
    isConnected_iff_connectedSpace.mp (PeriodDomain.Multiplicity.native_domain_connected E P hg.reference_admissible)
  have hf : Continuous f := PeriodDomain.Multiplicity.nativePeriod_halfDet_continuous E P hg.reference_admissible hμ v hv e he (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ)
  have hs (x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) : f x ^ 2 = f z₀ ^ 2 :=
    (native_theta_scalar_for_period hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ x).2.1.trans
      (native_theta_scalar_for_period hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z₀).2.1.symm
  have heq := isPreconnected_univ.eq_of_sq_eq hf.continuousOn
    (continuous_const.continuousOn : ContinuousOn (fun _ : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} => f z₀) Set.univ)
    (fun x _ => hs x) (fun _ => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _) (Set.mem_univ z₀) rfl
  exact heq (Set.mem_univ z)

end

/-! The projected first theta derivative over the entire constructed
native period family has one rational-scalar covariance factor. -/

open scoped Classical _root_.Matrix

namespace Multiplicity

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

def nativeFrameTheta
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3) →ₗ[ℂ] ({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} → Fin 2 → ℂ) :=
  LinearMap.pi (fun z => RepresentationTheory.Hecke.RadialDilation.GeometricTheta.Realization.projectedFrameTheta P.distinguished (Multiplicity.Period.nativeLowerFrame E P hP v e z)
    (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z))

end Multiplicity

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity
attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_family_theta_covariance
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ) (hγ : γ.val = RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalScalarMatrix E e (r : E))
    (z₀ : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ D.pel.reference.domain}) (Φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) :
    Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he (D.weil.finiteAction γ Φ) =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) (PeriodFamily.Multiplicity.nativePeriod E D.pel.reference hg.reference_admissible hμ v hv e he z₀) *
        (D.pel.reference.embeddings D.pel.reference.distinguished (r : E))⁻¹) •
      Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he Φ := by
  funext z
  have h := (native_theta_scalar_for_period hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z).2.2 Φ
  rw [native_halfDet_constant hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z₀ z] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta
