import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointOne

/-! # Local Rational -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalRational

noncomputable section

/-! Rational compatibility of the quaternion map at one finite place. -/

open scoped Classical _root_.NumberField

theorem unitaryFormCongr_comp_matrix {R G : Type*} [CommRing R] [StarRing R] [Group G]
    (H K : Matrix (Fin 3) (Fin 3) R) (h : H = K)
    (f : G →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H) (g : G) :
    ((CM.UnitaryPresentation.Quadratic.unitaryFormCongr H K h).toMonoidHom.comp f g).val.val = (f g).val.val := rfl

variable (F : Type) [Field F] [NumberField F] (a b : F)
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

theorem quaternionLocalUnitary_matrix
    (g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v)) :
    (LocalUnitary.quaternionLocalUnitary F a b v g).val.val =
      (PointOne.quaternionPointUnitary a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) g).val.val :=
  unitaryFormCongr_comp_matrix _ _ (LocalUnitary.localized_diagonalForm F a b (.inr v)).symm
    (PointOne.quaternionPointUnitary a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v))) g

theorem quaternionLocalUnitary_diagonal_matrix
    (g : (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)).RationalPoints) :
    (LocalUnitary.quaternionLocalUnitary F a b v
      (NumberTheory.Quaternion.Arithmetic.LocalAdeles.diagonalLocal (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v) g)).val.val =
      (PointOne.quaternionRationalUnitary a b g).val.val.map (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F a (.inr v)) := by
  rw [quaternionLocalUnitary_matrix]
  exact PointOne.quaternionPointUnitary_baseChange (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) a b g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalRational
