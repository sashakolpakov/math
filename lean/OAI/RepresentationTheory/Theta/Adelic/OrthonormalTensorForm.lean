import OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

/-! # Orthonormal Tensor Form -/

namespace OAI.RepresentationTheory.Theta.Adelic.OrthonormalTensorForm

noncomputable section

/-! The actual quadratic trace form in the specified orthonormal
coordinates, including its exact sign and factor of two. -/

open scoped Classical _root_.NumberField Kronecker

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.RealTensorCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

theorem formValue_inverse_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℂ) (B : (Matrix I I ℂ)ˣ) (x y : I → ℂ) :
    Weil.AdelicSplitting.TensorSpace.Construction.formValue Q x y = Weil.AdelicSplitting.TensorSpace.Construction.formValue (B.val.conjTranspose * Q * B.val)
      (B.inv.mulVec x) (B.inv.mulVec y) := by
  rw [← Weil.AdelicSplitting.TensorSpace.Construction.formValue_change, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    B.val_inv, Matrix.one_mulVec, Matrix.one_mulVec]

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem quadratic_trace_real_part (v : Fin A.places) (s : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))) :
    A.real v (QuadraticAlgebra.trace s / 2) = (A.complex v s).re := by
  have h := congrArg (A.complex v) (QuadraticAlgebra.algebraMap_trace_eq_add_star s)
  rw [A.complex_scalar, map_add, A.complex_star] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.add_re, Complex.star_def, Complex.conj_re] at hr
  rw [map_div₀, map_ofNat, hr]
  ring

theorem mapped_formValue {I : Type*} [Fintype I] [DecidableEq I]
    (v : Fin A.places) (Q : Matrix I I (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))))
    (x y : I → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))) :
    A.complex v (Weil.AdelicSplitting.TensorSpace.Construction.formValue Q x y) =
      Weil.AdelicSplitting.TensorSpace.Construction.formValue (Q.map (A.complex v)) (fun i => A.complex v (x i)) (fun i => A.complex v (y i)) := by
  simp only [Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct, map_sum, map_mul, A.complex_star, Matrix.map_apply]

theorem mapped_tensor_matrix (v : Fin A.places) :
    ((Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))) ⊗ₖ
      (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v)))).map (A.complex v) =
      (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))).map (A.complex v) ⊗ₖ
        (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))).map (A.complex v) := by
  apply Matrix.ext
  intro i j
  exact (A.complex v).map_mul _ _

theorem normalized_tensor_matrix (v : Fin A.places) :
    ((A.basisV v).val ⊗ₖ (A.basisP v).val).conjTranspose *
      (((Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))) ⊗ₖ
        (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v)))).map (A.complex v)) *
          ((A.basisV v).val ⊗ₖ (A.basisP v).val) =
      Matrix.diagonal (fun ij => Complex.I * ComplexPhaseCoordinates.tensorDualSign A (v, ij)) := by
  rw [mapped_tensor_matrix, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, A.formV, A.formP,
    Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext ij
  dsimp [ComplexPhaseCoordinates.tensorDualSign]
  split_ifs <;> ring

theorem orthonormal_trace_pairing (v : Fin A.places)
    (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    A.real v (Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m
      (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))
      (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))) x y) =
    (Weil.AdelicSplitting.TensorSpace.Construction.formValue (Matrix.diagonal (fun ij => Complex.I * ComplexPhaseCoordinates.tensorDualSign A (v, ij)))
      (RealTensorCoordinates.orthonormalTensorCoordinates A v (fun ij => A.complex v (x ij)))
      (RealTensorCoordinates.orthonormalTensorCoordinates A v (fun ij => A.complex v (y ij)))).re := by
  rw [Weil.AdelicSplitting.TensorSpace.Construction.tracePairing, quadratic_trace_real_part, mapped_formValue]
  rw [formValue_inverse_coordinates _
    (Matrix.GeneralLinearGroup.kronecker (A.basisV v) (A.basisP v))]
  change (Weil.AdelicSplitting.TensorSpace.Construction.formValue
    (((A.basisV v).val ⊗ₖ (A.basisP v).val).conjTranspose *
      (((Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))) ⊗ₖ
        (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v)))).map (A.complex v)) *
          ((A.basisV v).val ⊗ₖ (A.basisP v).val)) _ _).re = _
  rw [normalized_tensor_matrix]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.OrthonormalTensorForm
