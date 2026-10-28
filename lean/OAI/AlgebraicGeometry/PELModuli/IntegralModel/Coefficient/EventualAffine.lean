import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.AffineComparison

/-! # Eventual Affine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.EventualAffine.Coefficients

noncomputable section

/-! An affine generic fiber makes an actual finite-presentation
coefficient model affine after adjoining finitely many more coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem coefficient_model_eventually_affine {X : Over (Spec (.of K))} [IsAffine X.left]
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (M : Models.Coefficients.CoefficientModel R K X) :
    ∃ (t : Finset K) (h : M.coefficients ⊆ t),
      IsAffine ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M.model).left := by
  classical
  obtain ⟨A, hA⟩ := Affine.CoefficientModels.Coefficients.isAffine_has_affine_coefficient_model (R := R) X hX
  let t := M.coefficients ∪ A.coefficients
  have hMt : M.coefficients ⊆ t := Finset.subset_union_left
  have hAt : A.coefficients ⊆ t := Finset.subset_union_right
  let M₀ := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hMt)).obj M.model
  let A₀ := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hAt)).obj A.model
  have : IsAffine A.model.left := hA
  have : IsAffine A₀.left := AffineBaseChange.Coefficients.affine_baseChange (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hAt) A.model
  obtain ⟨z, htz, hz⟩ := AffineComparison.Coefficients.affine_comparison_eventually
    M₀ A₀ (Finiteness.Coefficients.baseChange_finitePresentation _ _ M.finitePresentation)
    (Finiteness.Coefficients.baseChange_finitePresentation _ _ A.finitePresentation)
    (Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hMt)
    (Morphisms.Coefficients.genericModelLift A.model A.specialization A.cartesian.w hAt)
    (Morphisms.Coefficients.genericModelLift_cartesian M.model M.specialization M.cartesian hMt)
    (Morphisms.Coefficients.genericModelLift_cartesian A.model A.specialization A.cartesian hAt)
  exact ⟨z, hMt.trans htz, AffineComparison.Coefficients.affine_coefficient_baseChange_trans hMt htz M.model hz⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.EventualAffine.Coefficients
