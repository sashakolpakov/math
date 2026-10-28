import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianAction
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFieldActionRecovery
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussian

/-! # Intrinsic Local Action Parameter -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalActionParameter.Intrinsic

noncomputable section

/-! The actual native SU operator determines its real phase-space
action from the full oscillator identification. Local normalization
only removes the nonzero scalar of the given Gaussian representative. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianValues.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianAction.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg OAI.RepresentationTheory.Theta.Kernel.IntrinsicFieldActionRecovery.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussian.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicBounds

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P}

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

def normalizedNativeLocal (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (v : Fin A.places) :
    Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) (3 * m) :=
  (((B.gaussian z ξ) (A.enumerate v)).val 0)⁻¹ • (B.gaussian z ξ) (A.enumerate v)

def localActionScalar (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (v : Fin A.places) : ℂ :=
  (((B.gaussian z ξ) (A.enumerate v)).val 0)⁻¹ *
    ((Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (B.gaussian z ξ)) (A.enumerate v)).val 0

theorem normalized_native_action (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (v : Fin A.places)
    (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl (A.enumerate v)) (g (A.enumerate v)))
      (normalizedNativeLocal B z ξ v)).val (fun i => (A.real v).symm (x i)) =
        localActionScalar B (D := D) g z ξ v *
          IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period (B.ball g • z))).matrix
            (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ((B.symplectic g).jacobiChange (B.period z) ξ)) x := by
  have h := IntrinsicLocalGaussianAction.Intrinsic.native_local_action_gaussian B hO g z ξ
  let a0 := ((Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (B.gaussian z ξ)) (A.enumerate v)).val 0
  have hv := congrArg (fun t : ℂ => a0 * t) (h.2 v x)
  dsimp only [a0] at hv
  simp only [← mul_assoc,mul_inv_cancel₀ (h.1 v),one_mul] at hv
  unfold normalizedNativeLocal
  rw [map_smul]
  change (((B.gaussian z ξ) (A.enumerate v)).val 0)⁻¹ *
    ((Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (B.gaussian z ξ)) (A.enumerate v)).val
      (fun i => (A.real v).symm (x i)) = _
  rw [hv]
  exact (mul_assoc _ _ _).symm

theorem native_local_action_parameter (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (v : Fin A.places)
    (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ)
    (hξ : IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ξ = IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix q p) :
    let w := Weil.Local.FunctionsMetaplectic.Construction.symplecticAction
      (Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) (3 * m)
        (Weil.AdelicSplitting.Oscillator.Construction.localProjection _ _ _ (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl (A.enumerate v)) (g (A.enumerate v)))))
      (Sum.elim q p)
    IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period (B.ball g • z))).matrix
      (fun i => w (.inl i)) (fun i => w (.inr i)) =
      IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ((B.symplectic g).jacobiChange (B.period z) ξ) := by
  let : SecondCountableTopology (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) :=
    (show Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v)) ≃ₜ ℝ from
      ⟨(A.real v).toEquiv,A.real_continuous v,A.real_inverse_continuous v⟩).secondCountableTopology
  have hz (W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin (3 * m))) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
      IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian W.matrix 0 x = Weil.Local.SiegelGaussian.Construction.siegelGaussian W.matrix x := by
    simp [IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian,IntrinsicGaussianUniqueness.IntrinsicBounds.siegel_gaussian_phase,IntrinsicGaussianUniqueness.IntrinsicBounds.phaseGaussian]
  apply IntrinsicFieldActionRecovery.Intrinsic.field_gaussian_action_parameter (A.real v) (A.real_continuous v) (A.real_inverse_continuous v)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))) (IntrinsicLocalGaussian.Intrinsic.standard_arch_field_character A C.ψ hψ v)
    (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl (A.enumerate v)) (g (A.enumerate v)))
    (normalizedNativeLocal B z 0 v) (normalizedNativeLocal B z ξ v)
    (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)) (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period (B.ball g • z)))
    q p _ (localActionScalar B (D := D) g z 0 v) (localActionScalar B (D := D) g z ξ v)
  · exact mul_ne_zero (inv_ne_zero (IntrinsicLocalGaussianValues.Intrinsic.native_local_gaussian_zero_ne B hO z 0 v))
      ((IntrinsicLocalGaussianAction.Intrinsic.native_local_action_gaussian B hO g z 0).1 v)
  · intro x
    change (((B.gaussian z 0) (A.enumerate v)).val 0)⁻¹ *
      ((B.gaussian z 0) (A.enumerate v)).val (fun i => (A.real v).symm (x i)) = _
    rw [IntrinsicLocalGaussianValues.Intrinsic.normalized_local_gaussian_value B hO]
    simpa only [IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi,Matrix.mulVec_zero] using hz (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)) x
  · intro x
    change (((B.gaussian z ξ) (A.enumerate v)).val 0)⁻¹ *
      ((B.gaussian z ξ) (A.enumerate v)).val (fun i => (A.real v).symm (x i)) = _
    rw [IntrinsicLocalGaussianValues.Intrinsic.normalized_local_gaussian_value B hO,hξ]
  · intro x
    rw [normalized_native_action B hO]
    simp only [map_zero,IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi,Matrix.mulVec_zero,hz]
  · exact normalized_native_action B hO g z ξ v

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalActionParameter.Intrinsic
