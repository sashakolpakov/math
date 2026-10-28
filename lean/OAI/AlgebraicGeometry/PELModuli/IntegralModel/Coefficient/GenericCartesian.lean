import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericIsomorphism
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.ComparisonIsomorphism

/-! # Generic Cartesian -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericCartesian.Coefficients

noncomputable section

/-! An actual cartesian generic-fiber comparison becomes cartesian over
a finite enlargement of the coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem coefficient_generic_cartesian_after_enlargement
    {R K : Type} [CommRing R] [Field K] [Algebra R K] {s : Finset K}
    {W X Y Z : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)}
    (a : W ⟶ X) (b : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hw : a ≫ f = b ≫ g)
    (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom)
    (hP : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback f g).hom)
    (hc : IsPullback ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map a)
      ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map b)
      ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map f)
      ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map g)) :
    ∃ (t : Finset K) (hst : s ⊆ t),
      IsPullback ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map a)
        ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map b)
        ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map f)
        ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)).map g) := by
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let c : W ⟶ pullback f g := pullback.lift a b hw
  have ha : F.map c ≫ F.map (pullback.fst f g) = F.map a := by
    rw [← F.map_comp, pullback.lift_fst]
  have hb : F.map c ≫ F.map (pullback.snd f g) = F.map b := by
    rw [← F.map_comp, pullback.lift_snd]
  have : IsIso (F.map c) := Cartesian.ComparisonIsomorphism.isIso_of_cartesian_comparison hc
    ((IsPullback.of_hasPullback f g).map F) (F.map c) ha hb
  obtain ⟨t, hst, hi⟩ := GenericIsomorphism.Coefficients.coefficient_generic_isIso_after_enlargement W (pullback f g) hW hP c
  let H := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K hst)
  refine ⟨t, hst, Cartesian.ComparisonIsomorphism.isPullback_of_isIso_comparison ((IsPullback.of_hasPullback f g).map H)
    (H.map c) ?_ ?_⟩
  · rw [← H.map_comp, pullback.lift_fst]
  · rw [← H.map_comp, pullback.lift_snd]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericCartesian.Coefficients
