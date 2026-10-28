import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicFrameRoot
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaFamilyTransfer
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScaledFrameProjection

/-! # Cotangent Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity

noncomputable section

/-! Normalize the native cotangent projection by the constructed
holomorphic frame root. This preserves every input relation and the
whole-family dilation identity. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

def nativeCotangentProjection (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (((Fin s × Fin 3) → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent :=
  (HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension E P hP hμ v hv e he z)⁻¹ • ThetaCoordinates.Multiplicity.nativeThetaProjection E P hP v e z

theorem nativeCotangentProjection_differentiable :
    DifferentiableOn ℂ (nativeCotangentProjection E P hP hμ v hv e he) P.domain := by
  unfold nativeCotangentProjection ThetaCoordinates.Multiplicity.nativeThetaProjection
  have hq : ∀ z ∈ P.domain, Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) P.distinguished
      (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0 := by
    intro z _
    rw [Multiplicity.Period.native_frame_denominator E P z]
    exact (map_ne_zero _).mpr hP.2.2.1
  have hQ : DifferentiableOn ℂ (Multiplicity.Period.nativeLowerFrame E P hP v e) P.domain :=
    PeriodFrameFamilies.Multiplicity.lowerFrame_differentiable (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1 e)
      (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P)) P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) P.domain hq
  exact ScaledFrameProjection.Multiplicity.scaled_frameProjection_differentiable (ι := Fin s × Fin 3) P.domain
    (fun i : Fin 2 => (P.distinguished, i.succ))
    (fun z => (HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension E P hP hμ v hv e he z)⁻¹)
    (Multiplicity.Period.nativeLowerFrame E P hP v e)
    ((HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension_differentiable E P hP hμ v hv e he).inv
      (fun z _ => HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension_ne_zero E P hP hμ v hv e he z)) hQ
    (PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he)

def nativeCotangentThetaOneForm :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3) →ₗ[ℂ] (RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
  RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear (ThetaCoordinates.Multiplicity.nativeThetaPeriod E P hP hμ v hv e he)
    (nativeCotangentProjection E P hP hμ v hv e he)

theorem nativeCotangentThetaOneForm_eq (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    nativeCotangentThetaOneForm E P hP hμ v hv e he φ z =
      (HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension E P hP hμ v hv e he z)⁻¹ • ThetaCoordinates.Multiplicity.nativeThetaOneForm E P hP hμ v hv e he φ z := rfl

theorem nativeCotangentThetaOneForm_holomorphic (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) :
    DifferentiableOn ℂ (nativeCotangentThetaOneForm E P hP hμ v hv e he φ) P.domain :=
  RepresentationTheory.Theta.Geometric.LinearTheta.canonical_oneForm_holomorphic P.domain _ (ThetaCoordinates.Multiplicity.nativeThetaPeriod_differentiable E P hP hμ v hv e he)
    _ (nativeCotangentProjection_differentiable E P hP hμ v hv e he) φ

theorem nativeCotangentThetaOneForm_coordinates (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (z : {z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain}) :
    nativeCotangentThetaOneForm E P hP hμ v hv e he φ z =
      (FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he z)⁻¹ •
        FrameProjection.Multiplicity.coordinateCovector (FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he φ z) := by
  rw [nativeCotangentThetaOneForm_eq, HolomorphicFrameRoot.Multiplicity.nativeFrameRootExtension_on_domain E P hP hμ v hv e he z z.property,
    ThetaCoordinates.Multiplicity.nativeThetaOneForm_coordinates]

def nativeCotangentFamilyEquiv :
    ({z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain} → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) ≃ₗ[ℂ]
      ({z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain} → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
  LinearEquiv.piCongrRight fun z => LinearEquiv.smulOfNeZero ℂ RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent
    (FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he z)⁻¹ (inv_ne_zero (FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he z))

def nativeCotangentThetaOnDomain :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3) →ₗ[ℂ] ({z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain} → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
  (nativeCotangentFamilyEquiv E P hP hμ v hv e he).toLinearMap.comp
    (ThetaFamilyTransfer.Multiplicity.nativeThetaOnDomain E P hP hμ v hv e he)

theorem nativeCotangentThetaOnDomain_apply (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (z : {z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain}) :
    nativeCotangentThetaOnDomain E P hP hμ v hv e he φ z =
      nativeCotangentThetaOneForm E P hP hμ v hv e he φ z := by
  rw [nativeCotangentThetaOneForm_coordinates]
  rfl

theorem nativeCotangentThetaOnDomain_ker :
    LinearMap.ker (nativeCotangentThetaOnDomain E P hP hμ v hv e he) =
      LinearMap.ker (FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he) := by
  calc
    _ = LinearMap.ker (ThetaFamilyTransfer.Multiplicity.nativeThetaOnDomain E P hP hμ v hv e he) := by
      ext φ
      exact (nativeCotangentFamilyEquiv E P hP hμ v hv e he).map_eq_zero_iff
    _ = _ := ThetaFamilyTransfer.Multiplicity.nativeThetaOnDomain_ker E P hP hμ v hv e he

theorem nativeCotangentThetaOnDomain_dilation {q M : ℕ} [Fact q.Prime] (ω : ℂ)
    (j : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (h : ∀ b, FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
      ω • FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j b)) :
    ∀ b, nativeCotangentThetaOnDomain E P hP hμ v hv e he (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
      ω • nativeCotangentThetaOnDomain E P hP hμ v hv e he (j b) := by
  intro b
  change (nativeCotangentFamilyEquiv E P hP hμ v hv e he)
    (ThetaFamilyTransfer.Multiplicity.nativeThetaOnDomain E P hP hμ v hv e he (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b))) = _
  rw [ThetaFamilyTransfer.Multiplicity.nativeThetaOnDomain_dilation E P hP hμ v hv e he ω j h b, map_smul]
  rfl

theorem nativeCotangentThetaOnDomain_finite {q M : ℕ} [Fact q.Prime] (hM : 0 < M)
    (ω : ℂ) (hω : ω ≠ 0)
    (j : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (h : ∀ b, FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he
      (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
        ω • FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j b)) :
    FiniteDimensional ℂ (LinearMap.range
      ((nativeCotangentThetaOnDomain E P hP hμ v hv e he).comp j)) :=
  Radial.Dilation.radial_image_finiteDimensional q _ M hM ω hω
    (nativeCotangentThetaOnDomain_dilation E P hP hμ v hv e he ω j h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentTheta.Multiplicity
