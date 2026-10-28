import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.CoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CommonStage

/-! # Source Enlargement -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement.Coefficients

/-! Specialization from the actual generic fiber to a fixed-source
coefficient model preserves the original ambient scheme projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem fixedSourceModel_specialization_fst (s : Finset K) (X : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization ≫ pullback.fst X.hom (CoefficientModels.Coefficients.parameterBaseMap R K s) =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let f := CoefficientModels.Coefficients.parameterBaseMap R K s
  let g := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let e := (CoefficientModels.Coefficients.fixedSourceComparison R K s).app X
  have he : e.hom.left ≫ pullback.fst X.hom b =
      pullback.fst (pullback.snd X.hom f) g ≫ pullback.fst X.hom f :=
    Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst X f g b (CoefficientModels.Coefficients.generic_parameterBaseMap R K s)
  change (e.inv.left ≫ pullback.fst (pullback.snd X.hom f) g) ≫ pullback.fst X.hom f = _
  rw [Category.assoc, ← he, Over.inv_left_hom_left_assoc]

end AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement.Coefficients

namespace AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement

/-! A coefficient enlargement of a fixed-source model is the actual
fixed-source model at the larger stage, compatibly with specialization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Coefficients
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {s t : Finset K} (h : s ⊆ t) (X : Over (Spec (.of R)))

def fixedSourceEnlargementIso :
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).obj
        ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X) ≅
      (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K t)).obj X :=
  (Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (CoefficientModels.Coefficients.parameterBaseMap R K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
    (CoefficientModels.Coefficients.parameterBaseMap R K t) (CoefficientModels.Coefficients.coefficient_parameterBaseMap R K h)).app X

theorem fixedSourceEnlargement_generic (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    Coefficient.Morphisms.Coefficients.genericModelLift (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).model
        (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).cartesian.w h ≫
      (fixedSourceEnlargementIso h X).hom.left = (CoefficientModels.Coefficients.fixedSourceModel R K t X hX).specialization := by
  let e := fixedSourceEnlargementIso h X
  have hf : e.hom.left ≫ pullback.fst X.hom (CoefficientModels.Coefficients.parameterBaseMap R K t) =
      pullback.fst (pullback.snd X.hom (CoefficientModels.Coefficients.parameterBaseMap R K s)) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) ≫
        pullback.fst X.hom (CoefficientModels.Coefficients.parameterBaseMap R K s) :=
    Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst X (CoefficientModels.Coefficients.parameterBaseMap R K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
      (CoefficientModels.Coefficients.parameterBaseMap R K t) (CoefficientModels.Coefficients.coefficient_parameterBaseMap R K h)
  have hs : e.hom.left ≫ pullback.snd X.hom (CoefficientModels.Coefficients.parameterBaseMap R K t) =
      pullback.snd (pullback.snd X.hom (CoefficientModels.Coefficients.parameterBaseMap R K s)) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h) := e.hom.w
  have hfst := Coefficient.Morphisms.Coefficients.genericModelLift_fst (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).model
    (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).cartesian.w h
  have hsnd := Coefficient.Morphisms.Coefficients.genericModelLift_snd (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).model
    (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).cartesian.w h
  apply pullback.hom_ext
  · rw [Category.assoc, hf, ← Category.assoc]
    exact (congrArg (fun a => a ≫ pullback.fst X.hom (CoefficientModels.Coefficients.parameterBaseMap R K s)) hfst).trans
      ((fixedSourceModel_specialization_fst s X hX).trans
        (fixedSourceModel_specialization_fst t X hX).symm)
  · rw [Category.assoc, hs]
    exact hsnd.trans (CoefficientModels.Coefficients.fixedSourceModel R K t X hX).cartesian.w.symm

end Coefficients

end AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement

end

end OAI
