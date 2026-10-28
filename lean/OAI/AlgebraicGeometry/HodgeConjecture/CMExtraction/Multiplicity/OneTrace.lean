import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneFrames
import OAI.NumberTheory.ArithmeticGroups.Data

/-! # One Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneTrace.Quadratic

noncomputable section

/-! The one-line unitary tensor has exactly the original rational trace
pairing. Its skew coefficient compensates for AdelicSplitting's half-trace and its
conjugate-linear first argument. -/

open scoped Classical Kronecker
open _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)

def singleTensorPosition (x : Fin 3 → E) : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 3 1 :=
  fun ij => (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm (x ij.1)

theorem singleSkewUnit_matrix :
    (OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 a ha ha0).val =
      Matrix.diagonal (fun _ : Fin 1 => (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm (-2 * δ * a)) := by
  apply Matrix.ext
  intro i j
  apply (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).injective
  rw [OneFrames.Quadratic.singleSkewUnit_evaluation]
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp only [Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]

theorem single_tensor_form (x y : Fin 3 → E) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue ((ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val ⊗ₖ
        (OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 a ha ha0).val)
      (singleTensorPosition E δ hδ hδ0 x) (singleTensorPosition E δ hδ hδ0 y) =
      (-2 * (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm δ) *
        star ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm (a * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)) := by
  rw [ThetaCycle.CMGlobalFrames.CM.cm_hermitian_unit_val E δ hδ hδ0, singleSkewUnit_matrix]
  rw [← ThetaCycle.QuadraticModel.CM.cm_quadratic_equiv_conjugation E δ hδ hδ0 (a * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)]
  apply (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).injective
  simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, ThetaCycle.QuadraticTensor.CM.quadraticHermitianMatrix, Matrix.diagonal_kronecker_diagonal,
    Matrix.mulVec_diagonal, dotProduct, singleTensorPosition,
    ← ThetaCycle.QuadraticModel.CM.cm_quadratic_equiv_conjugation, map_sum, map_mul, map_neg, map_ofNat,
    AlgEquiv.apply_symm_apply]
  simp only [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, map_sum, map_mul, IsCMField.complexConj_apply_apply,
    ha, apply_ite, hb, map_one, Fintype.sum_prod_type, Fin.sum_univ_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem single_tensor_rational_trace (x y : Fin 3 → E) :
    Algebra.trace ℚ (maximalRealSubfield E)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 3 1
        (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val (OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 a ha ha0).val
        (singleTensorPosition E δ hδ hδ0 x) (singleTensorPosition E δ hδ hδ0 y)) =
      Algebra.trace ℚ E (δ * (a * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)) := by
  have hd : star ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm δ) =
      -(ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm δ := by
    rw [← ThetaCycle.QuadraticModel.CM.cm_quadratic_equiv_conjugation, hδ, map_neg]
  rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing, single_tensor_form E δ hδ hδ0 b hb hb0 a ha ha0 x y,
    ThetaCycle.QuadraticModel.CM.quadratic_skew_trace_normalization _ _ _ hd,
    ThetaCycle.QuadraticModel.CM.cm_quadratic_rational_trace E δ hδ hδ0, map_mul,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneTrace.Quadratic
