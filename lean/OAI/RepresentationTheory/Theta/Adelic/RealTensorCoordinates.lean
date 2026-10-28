import OAI.RepresentationTheory.Theta.Adelic.TensorFrameTopology
import OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates

/-! # Real Tensor Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealTensorCoordinates

noncomputable section

/-! The actual native real tensor space in the prescribed orthonormal
complex bases. This is a real-linear equivalence constructed from the
given AdelicSplitting frames and completion isomorphisms. -/

open scoped Classical _root_.NumberField Kronecker

open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TensorFrameTopology OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def orthonormalTensorCoordinates (v : Fin A.places) :
    (Fin 3 × Fin m → ℂ) ≃L[ℂ] (Fin 3 × Fin m → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv (Matrix.GeneralLinearGroup.toLin
    (Matrix.GeneralLinearGroup.kronecker (A.basisV v)⁻¹ (A.basisP v)⁻¹)).toLinearEquiv

def realTensorAddEquiv (v : Fin A.places) :
    Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m) ≃+ (Fin 3 × Fin m → ℂ) :=
  (AddEquiv.piCongrRight (fun _ => (A.real v).symm.toAddEquiv)).trans
    ((P.localFrame (.inl (A.enumerate v))).coordinates.symm.toAddEquiv.trans
      ((AddEquiv.piCongrRight (fun _ => (A.complex v).toAddEquiv)).trans
        (orthonormalTensorCoordinates A v).toLinearEquiv.toAddEquiv))

theorem realTensorAddEquiv_continuous (v : Fin A.places) :
    Continuous (realTensorAddEquiv A P v) := by
  apply (orthonormalTensorCoordinates A v).continuous.comp
  apply (continuous_pi (fun ij => (A.complex_continuous v).comp (continuous_apply ij))).comp
  apply (TensorFrameTopology.frame_inverse_continuous _ (P.localFrame (.inl (A.enumerate v)))).comp
  exact continuous_pi (fun i => (A.real_inverse_continuous v).comp (continuous_apply i))

theorem realTensorAddEquiv_inverse_continuous (v : Fin A.places) :
    Continuous (realTensorAddEquiv A P v).symm := by
  apply (continuous_pi (fun i => (A.real_continuous v).comp (continuous_apply i))).comp
  apply (TensorFrameTopology.frame_continuous _ (P.localFrame (.inl (A.enumerate v)))).comp
  apply (continuous_pi (fun ij => (A.complex_inverse_continuous v).comp (continuous_apply ij))).comp
  exact (orthonormalTensorCoordinates A v).symm.continuous

def realTensorEquiv (v : Fin A.places) :
    Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m) ≃L[ℝ] (Fin 3 × Fin m → ℂ) :=
  (realTensorAddEquiv A P v).toRealLinearEquiv
    (realTensorAddEquiv_continuous A P v) (realTensorAddEquiv_inverse_continuous A P v)

theorem realTensorEquiv_native (v : Fin A.places)
    (s : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    realTensorEquiv A P v (fun i => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates s i)) =
        ((A.basisV v).inv ⊗ₖ (A.basisP v).inv).mulVec (fun ij => A.complex v (s ij)) := by
  have he : (fun i => (A.real v).symm (A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates s i))) =
        (P.localFrame (.inl (A.enumerate v))).coordinates s := by
    funext i
    exact (A.real v).symm_apply_apply _
  change orthonormalTensorCoordinates A v (fun ij => A.complex v
    ((P.localFrame (.inl (A.enumerate v))).coordinates.symm
      (fun i => (A.real v).symm (A.real v
        ((P.localFrame (.inl (A.enumerate v))).coordinates s i))) ij)) = _
  rw [he, LinearEquiv.symm_apply_apply]
  rfl

def totalRealTensorEquiv :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) ≃L[ℝ] (Fin A.places → Fin 3 × Fin m → ℂ) :=
  (PhaseCoordinates.realPhaseCoordinates A).symm.trans
    (ContinuousLinearEquiv.piCongrRight (realTensorEquiv A P))

end

end OAI.RepresentationTheory.Theta.Adelic.RealTensorCoordinates
