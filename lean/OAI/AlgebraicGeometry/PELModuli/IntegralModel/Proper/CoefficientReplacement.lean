import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.ClosedEmbeddings
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericClosedModels

/-! # Coefficient Replacement -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoefficientReplacement.Coefficients

noncomputable section

/-! Replace a coefficient model of an ambient-field closed subscheme by
its proper schematic closure, without assuming that the ambient field
is the fraction field of the finite coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
  {s : Finset K}

theorem proper_coefficient_replacement
    (M P : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) [IsProper P.hom] (f : M ⟶ P)
    [IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map f).left] :
    ∃ (N : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) (j : N ⟶ P),
      IsClosedImmersion j.left ∧ IsProper N.hom ∧ ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism N.hom ∧
        Nonempty ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj N ≅
          (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj M) := by
  have : IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s) := Coefficient.Finiteness.Coefficients.coefficientBase_locallyNoetherian R K s
  let g := Coefficient.FractionField.Coefficients.fractionBaseMap R K s
  let ψ := Coefficient.FractionField.Coefficients.ambientFieldMap R K s
  let F := Over.pullback g
  have : QuasiCompact g := by unfold g Coefficient.FractionField.Coefficients.fractionBaseMap; infer_instance
  have : IsClosedImmersion (F.map f).left := Coefficient.ClosedEmbeddings.Coefficients.closedImmersion_fraction_model f
  obtain ⟨N, j, hj, hp, hfp, e, _⟩ := GenericClosedModels.closed_generic_model_with_embedding g P (F.obj M) (F.map f)
  let c (Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)) :=
    Group.BaseChangeComparisons.GroupBaseChange.iteratedIso Y g ψ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) (Coefficient.FractionField.Coefficients.fractionBase_factorization R K s)
  exact ⟨N, j, hj, hp, hfp,
    ⟨(c N).symm ≪≫ (Over.pullback ψ).mapIso e ≪≫ c M⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoefficientReplacement.Coefficients
