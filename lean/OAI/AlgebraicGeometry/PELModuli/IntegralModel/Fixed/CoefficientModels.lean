import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Coefficient Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.CoefficientModels.Coefficients

noncomputable section

/-! Finite coefficient parameters over a fixed arithmetic base, and the
constant source models obtained from actual base change of that source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def parameterBaseMap (s : Finset K) : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s)))

theorem generic_parameterBaseMap (s : Finset K) :
    ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s ≫ parameterBaseMap R K s =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  dsimp only [parameterBaseMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientCocone]
  rw [← Spec.map_comp]
  congr 1

theorem coefficient_parameterBaseMap {s t : Finset K} (h : s ⊆ t) :
    ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h ≫ parameterBaseMap R K s = parameterBaseMap R K t := by
  dsimp only [parameterBaseMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram]
  rw [← Spec.map_comp]
  congr 1

def coefficientParameter (s : Finset K) : Over (Spec (.of R)) := Over.mk (parameterBaseMap R K s)

def fixedSourceComparison (s : Finset K) :
    Over.pullback (parameterBaseMap R K s) ⋙ Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (parameterBaseMap R K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (generic_parameterBaseMap R K s)

theorem coefficientParameter_locallyOfFiniteType (s : Finset K) :
    LocallyOfFiniteType (coefficientParameter R K s).hom := by
  have : Algebra.FiniteType R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType R K s
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

def fixedSourceModel (s : Finset K) (X : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    Coefficient.Models.Coefficients.CoefficientModel R K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X) := by
  let f := parameterBaseMap R K s
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  exact {
    coefficients := s
    model := (Over.pullback f).obj X
    finitePresentation := ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom f)),
      inferInstanceAs (QuasiCompact (pullback.snd X.hom f)),
      inferInstanceAs (QuasiSeparated (pullback.snd X.hom f))⟩
    genericIso := (fixedSourceComparison R K s).app X }

theorem fixedSourceModel_smooth_proper (s : Finset K) (X : Over (Spec (.of R)))
    [Smooth X.hom] [IsProper X.hom] :
    let D := fixedSourceModel R K s X ⟨inferInstance, inferInstance, inferInstance⟩
    Smooth D.model.hom ∧ IsProper D.model.hom := by
  exact ⟨inferInstanceAs (Smooth (pullback.snd X.hom (parameterBaseMap R K s))),
    inferInstanceAs (IsProper (pullback.snd X.hom (parameterBaseMap R K s)))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.CoefficientModels.Coefficients
