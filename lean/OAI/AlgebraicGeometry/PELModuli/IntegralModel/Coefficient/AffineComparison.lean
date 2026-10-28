import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Isomorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.AffineBaseChange

/-! # Affine Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.AffineComparison.Coefficients

noncomputable section

/-! Affineness transfers between two coefficient models with the
same actual generic fiber after a finite coefficient enlargement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem affine_comparison_eventually {s : Finset K} {X : Over (Spec (.of K))}
    (M A : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [IsAffine A.left]
    (hM : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism M.hom) (hA : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism A.hom)
    (pM : X.left ⟶ M.left) (pA : X.left ⟶ A.left)
    (hcM : IsPullback pM X.hom M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s))
    (hcA : IsPullback pA X.hom A.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)) :
    ∃ (t : Finset K) (h : s ⊆ t),
      IsAffine ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj M).left := by
  obtain ⟨t, h, e, _⟩ := Isomorphisms.Coefficients.isomorphism_between_models_descends M A hM hA pM pA hcM hcA (Iso.refl X)
  have : IsAffine ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj A).left :=
    AffineBaseChange.Coefficients.affine_baseChange (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) A
  exact ⟨t, h, AffineBaseChange.Coefficients.affine_of_over_iso e⟩

theorem affine_coefficient_baseChange_trans {s t z : Finset K} (hst : s ⊆ t) (htz : t ⊆ z)
    (M : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s))
    (hM : IsAffine ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K htz)).obj
      ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).obj M)).left) :
    IsAffine ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K (hst.trans htz))).obj M).left := by
  have := hM
  exact AffineBaseChange.Coefficients.affine_of_over_iso (BaseChange.Coefficients.coefficientBaseChangeTrans hst htz M).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.AffineComparison.Coefficients
