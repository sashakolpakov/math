import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Family
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation

/-! # Theta Family Transfer -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaFamilyTransfer.Multiplicity

noncomputable section

/-! Transfer the constructed theta-family dilation to the exact native
cotangent-valued functions. Coordinate conversion is an equivalence. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open scoped Classical _root_.Matrix

def coordinateCovectorEquiv : (Fin 2 → ℂ) ≃ₗ[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent where
  __ := FrameProjection.Multiplicity.coordinateCovector
  invFun := RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector
  left_inv a := by
    funext i
    simp [RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector, FrameProjection.Multiplicity.coordinateCovector_apply, Pi.single_apply]
  right_inv l := by
    apply ContinuousLinearMap.ext
    intro x
    change FrameProjection.Multiplicity.coordinateCovector (RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector l) x = l x
    rw [FrameProjection.Multiplicity.coordinateCovector_apply, RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.cotangent_expansion l x]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def cotangentFamilyEquiv (X : Type) : (X → Fin 2 → ℂ) ≃ₗ[ℂ] (X → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
  LinearEquiv.piCongrRight (fun _ => coordinateCovectorEquiv)

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))

def nativeThetaOnDomain :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3) →ₗ[ℂ] ({z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain} → RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
  (cotangentFamilyEquiv _).toLinearMap.comp (Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he)

theorem nativeThetaOnDomain_apply (Φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (z : {z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates // z ∈ P.domain}) :
    nativeThetaOnDomain E P hP hμ v hv e he Φ z =
      Intrinsic.ThetaCoordinates.Multiplicity.nativeThetaOneForm E P hP hμ v hv e he Φ z :=
  (Intrinsic.ThetaCoordinates.Multiplicity.nativeThetaOneForm_coordinates E P hP hμ v hv e he Φ z).symm

theorem nativeThetaOnDomain_ker :
    LinearMap.ker (nativeThetaOnDomain E P hP hμ v hv e he) =
      LinearMap.ker (Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he) := by
  ext Φ
  change (cotangentFamilyEquiv _) (Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he Φ) = 0 ↔ _
  exact (cotangentFamilyEquiv _).map_eq_zero_iff

theorem nativeThetaOnDomain_dilation {q M : ℕ} [Fact q.Prime] (ω : ℂ)
    (j : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (h : ∀ b, Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
      ω • Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j b)) :
    ∀ b, nativeThetaOnDomain E P hP hμ v hv e he (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
      ω • nativeThetaOnDomain E P hP hμ v hv e he (j b) := by
  intro b
  change (cotangentFamilyEquiv _) (Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b))) = _
  rw [h b, map_smul]
  rfl

theorem nativeThetaOnDomain_finite {q M : ℕ} [Fact q.Prime] (hM : 0 < M)
    (ω : ℂ) (hω : ω ≠ 0) (j : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))
    (h : ∀ b, Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
      ω • Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he (j b)) :
    FiniteDimensional ℂ (LinearMap.range ((nativeThetaOnDomain E P hP hμ v hv e he).comp j)) :=
  Radial.Dilation.radial_image_finiteDimensional q _ M hM ω hω
    (nativeThetaOnDomain_dilation E P hP hμ v hv e he ω j h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaFamilyTransfer.Multiplicity
