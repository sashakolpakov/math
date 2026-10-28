import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.HermitianAdeles

/-! # Local Hermitian Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalHermitianMatrix

noncomputable section

/-! Expose the unchanged matrix of the transported local quaternion map
without unfolding its algebraic point construction. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (a b : F)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (hH : H.val = UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b))
  (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)

theorem quaternionLocalHermitian_matrix
    (g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v)) :
    (HermitianAdeles.quaternionLocalHermitian F a b H hH v g).val.val =
      (PointOne.quaternionPointUnitary a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) g).val.val :=
  (LocalRational.unitaryFormCongr_comp_matrix _ _
    (congrArg (fun M => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F M (.inr v)) hH.symm)
    (LocalUnitary.quaternionLocalUnitary F a b v) g).trans
    (LocalRational.quaternionLocalUnitary_matrix F a b v g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalHermitianMatrix
