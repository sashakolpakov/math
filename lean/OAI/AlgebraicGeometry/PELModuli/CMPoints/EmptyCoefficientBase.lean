import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticCoefficientEnlargement

/-! # Empty Coefficient Base -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EmptyCoefficientBase

noncomputable section

/-! The empty finite-coefficient stage is the original arithmetic ring.
This allows Foundations's fixed-model extension theorem to retain a supplied
arithmetic model instead of replacing it by a newly chosen model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R F : Type} [CommRing R] [Field F] [Algebra R F]

def emptyCoefficientEquiv (hi : Function.Injective (algebraMap R F)) :
    ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R F ∅ ≃ₐ[R] R :=
  (Subalgebra.equivOfEq _ _ (by simp [ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing])).trans (Algebra.botEquivOfInjective hi)

theorem emptyCoefficientEquiv_symm (hi : Function.Injective (algebraMap R F)) :
    (emptyCoefficientEquiv hi).symm.toRingHom = algebraMap R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R F ∅) := by
  apply RingHom.ext
  intro a
  exact (emptyCoefficientEquiv hi).symm.toAlgHom.commutes a

def coefficientStructureMap (s : Finset F) : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R F s ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R F s)))

theorem emptyCoefficientStructureMap_isIso (hi : Function.Injective (algebraMap R F)) :
    IsIso (coefficientStructureMap (R := R) (F := F) ∅) := by
  let e := Scheme.Spec.mapIso (emptyCoefficientEquiv hi).toRingEquiv.toCommRingCatIso.symm.op
  have he : e.hom = coefficientStructureMap (R := R) (F := F) ∅ := by
    change Spec.map (CommRingCat.ofHom (emptyCoefficientEquiv hi).symm.toRingHom) = _
    rw [emptyCoefficientEquiv_symm]
    rfl
  rw [← he]
  infer_instance

theorem genericBaseMap_structure (s : Finset F) :
    ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R F s ≫ coefficientStructureMap s =
      Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
  dsimp only [coefficientStructureMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientCocone]
  rw [← Spec.map_comp]
  rfl

theorem coefficientBaseMap_structure {s t : Finset F} (h : s ⊆ t) :
    ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R F h ≫ coefficientStructureMap s = coefficientStructureMap t := by
  dsimp only [coefficientStructureMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap, ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram]
  rw [← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EmptyCoefficientBase
