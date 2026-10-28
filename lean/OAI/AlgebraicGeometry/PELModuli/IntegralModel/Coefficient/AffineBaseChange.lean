import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.AffineBaseChange.Coefficients

noncomputable section

/-! Cached affine base-change and isomorphism comparisons for actual
coefficient models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem affine_baseChange {S T : Scheme.{0}} [IsAffine S] [IsAffine T]
    (f : T ⟶ S) (X : Over S) [IsAffine X.left] :
    IsAffine ((Over.pullback f).obj X).left :=
  inferInstanceAs (IsAffine (pullback X.hom f))

theorem affine_of_over_iso {S : Scheme.{0}} {X Y : Over S} (e : X ≅ Y)
    [IsAffine Y.left] : IsAffine X.left := by
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  exact isAffine_of_isAffineHom e.hom.left

theorem coefficientModel_enlarge_isAffine {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X : Over (Spec (.of K))} (M : Models.Coefficients.CoefficientModel R K X) [IsAffine M.model.left]
    (s : Finset K) (h : M.coefficients ⊆ s) : IsAffine (M.enlarge s h).model.left :=
  affine_baseChange (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) M.model

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.AffineBaseChange.Coefficients
