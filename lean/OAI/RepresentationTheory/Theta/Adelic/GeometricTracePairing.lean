import OAI.RepresentationTheory.Theta.Adelic.OrthonormalTensorForm

/-! # Geometric Trace Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricTracePairing

noncomputable section

/-! The complex symplectic form on the standard and dual components
restricts to the actual trace pairing on real tensor vectors. -/

open scoped Classical _root_.NumberField ComplexConjugate

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.RealTensorCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.OrthonormalTensorForm

theorem paired_trace_scalar (η x y : ℂ) (hη : η.im = 0) :
    (x * (η * conj y) - (η * conj x) * y) / (2 * Complex.I) =
      ((conj x * (Complex.I * η * y)).re : ℂ) := by
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, hη] <;> ring

theorem paired_trace_vector {I : Type*} [Fintype I] [DecidableEq I]
    (η : I → ℂ) (hη : ∀ i, (η i).im = 0) (x y : I → ℂ) :
    (∑ i, (x i * (η i * conj (y i)) - (η i * conj (x i)) * y i) / (2 * Complex.I)) =
      ((Weil.AdelicSplitting.TensorSpace.Construction.formValue (Matrix.diagonal (fun i => Complex.I * η i)) x y).re : ℂ) := by
  simp only [Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => paired_trace_scalar (η i) (x i) (y i) (hη i))

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def geometricPairing (x y : BallGeometryData.ComplexPhase A) : ℂ :=
  ∑ v, ∑ ij, ((x v).1 ij * (y v).2 ij - (x v).2 ij * (y v).1 ij) / (2 * Complex.I)

theorem tensorDualSign_im (i : BallGeometryData.FrameIndex A) : (ComplexPhaseCoordinates.tensorDualSign A i).im = 0 := by
  dsimp [ComplexPhaseCoordinates.tensorDualSign]
  split_ifs <;> norm_num

theorem realTensorComponents_pairing
    (x y : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    geometricPairing A (BallGeometryData.realTensorComponents A x) (BallGeometryData.realTensorComponents A y) =
      (∑ v, (A.real v (Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m
        (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))
        (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))) (x v) (y v)) : ℂ)) := by
  apply Finset.sum_congr rfl
  intro v _
  change (∑ ij,
    ((RealTensorCoordinates.orthonormalTensorCoordinates A v (fun ij => A.complex v (x v ij))) ij *
      (ComplexPhaseCoordinates.tensorDualSign A (v, ij) * conj ((RealTensorCoordinates.orthonormalTensorCoordinates A v
        (fun ij => A.complex v (y v ij))) ij)) -
      (ComplexPhaseCoordinates.tensorDualSign A (v, ij) * conj ((RealTensorCoordinates.orthonormalTensorCoordinates A v
        (fun ij => A.complex v (x v ij))) ij)) *
      (RealTensorCoordinates.orthonormalTensorCoordinates A v (fun ij => A.complex v (y v ij))) ij) /
        (2 * Complex.I)) = _
  rw [paired_trace_vector _ (fun ij => tensorDualSign_im A (v, ij)), OrthonormalTensorForm.orthonormal_trace_pairing]

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricTracePairing
