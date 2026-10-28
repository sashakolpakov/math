import OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates
import OAI.RepresentationTheory.Theta.Adelic.GeometricTracePairing
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase

/-! # Complex Symplectic Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.ComplexSymplecticPairing

noncomputable section

/-! The constructed complex coordinate equivalence preserves the
actual complexification of the trace symplectic form. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.GeometricTracePairing OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def geometricForm : BallGeometryData.ComplexPhase A →ₗ[ℂ] BallGeometryData.ComplexPhase A →ₗ[ℂ] ℂ :=
  (2 * Complex.I)⁻¹ • ∑ v : Fin A.places,
    (BilinearCoordinates.crossForm ℂ (Fin 3 × Fin m)).compl₁₂ (LinearMap.proj v) (LinearMap.proj v)

theorem geometricForm_apply (x y : BallGeometryData.ComplexPhase A) :
    geometricForm A x y = GeometricTracePairing.geometricPairing A x y := by
  simp only [geometricForm, LinearMap.smul_apply, LinearMap.sum_apply]
  change (2 * Complex.I)⁻¹ * (∑ v : Fin A.places,
    ((∑ ij, (x v).1 ij * (y v).2 ij) - (∑ ij, (x v).2 ij * (y v).1 ij))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  ring

variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem complexPhaseCoordinates_real_pairing
    (x y : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    GeometricTracePairing.geometricPairing A
      (ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun i => (x i : ℂ)))
      (ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun i => (y i : ℂ))) =
        DataTheta.standardPairing (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) := by
  obtain ⟨s, rfl⟩ := (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P).surjective x
  obtain ⟨t, rfl⟩ := (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P).surjective y
  have hs : ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun i => (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P s i : ℂ)) =
      BallGeometryData.realTensorComponents A s := ComplexPhaseCoordinates.complexPhaseCoordinates_native A P s
  have ht : ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun i => (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P t i : ℂ)) =
      BallGeometryData.realTensorComponents A t := ComplexPhaseCoordinates.complexPhaseCoordinates_native A P t
  rw [hs, ht, GeometricTracePairing.realTensorComponents_pairing]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv_pairing A P s t)
  simp only [DataTheta.standardPairing, Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_mul] at h
  exact h.symm

theorem complexPhaseCoordinates_pairing
    (x y : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :
    GeometricTracePairing.geometricPairing A (ComplexPhaseCoordinates.complexPhaseCoordinates A P x) (ComplexPhaseCoordinates.complexPhaseCoordinates A P y) =
      DataTheta.standardPairing x y := by
  have he : (geometricForm A).compl₁₂
      (ComplexPhaseCoordinates.complexPhaseCoordinates A P).toLinearEquiv.toLinearMap
      (ComplexPhaseCoordinates.complexPhaseCoordinates A P).toLinearEquiv.toLinearMap =
        BilinearCoordinates.standardForm ℂ (BallGeometryData.FrameIndex A) := by
    apply BilinearCoordinates.complexBilinear_ext_real
    intro u v
    rw [LinearMap.compl₁₂_apply, geometricForm_apply, BilinearCoordinates.standardForm_apply]
    exact complexPhaseCoordinates_real_pairing A P u v
  rw [← geometricForm_apply, ← BilinearCoordinates.standardForm_apply]
  exact congrArg (fun B => B x y) he

end

end OAI.RepresentationTheory.Theta.Adelic.ComplexSymplecticPairing
