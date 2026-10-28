import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.BasisCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ScalarPartialClass

/-! # Fraction Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FractionQuotient

noncomputable section

/-! A supported mixed fraction depends only on its numerator modulo
the actual point ideal. This permits the exact selected-fiber trace
numerator to be replaced by any genuine lift. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable (R : Type u) [CommRing R] {c m : ℕ} (s : Fin c → R) (t : Fin m → R)

def functional (a : R) : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m))) :=
  KoszulPoint.BasisCoordinates.functional R s t
    ((OrientedTopCohomology.evaluation R (Fin.append s t)).symm a)

theorem functional_eq (a : R) : functional R s t a =
    a • KoszulPartial.TopResidue.functional R := by
  have h := ScalarPartialClass.functional R (functional R s t a)
  have he : functional R s t a
      (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R)) = a :=
    (KoszulPoint.BasisCoordinates.evaluation R s t _).trans
      ((OrientedTopCohomology.evaluation R (Fin.append s t)).apply_symm_apply a)
  exact h.trans (congrArg (fun z => z • KoszulPartial.TopResidue.functional R) he)

theorem sourceClass_eq (a b : R)
    (h : Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) a =
      Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) b) :
    KoszulPartial.PartialClass.sourceClass R s t (functional R s t a) =
      KoszulPartial.PartialClass.sourceClass R s t (functional R s t b) := by
  let f := DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom
  have : IsIso f := by
    dsimp only [f, DualComplexHomology.map]
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso (homologyMap f (c+m))).injective
  change homologyMap (DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom)
    (c+m) _ = homologyMap (DualComplexHomology.map R
      (DuplicateFraction.pointIso R s t).hom) (c+m) _
  dsimp only [functional]
  rw [KoszulPoint.BasisCoordinates.class_coordinates,
    KoszulPoint.BasisCoordinates.class_coordinates]
  apply (ConcreteCategory.bijective_of_isIso
    (OrientedTopCohomology.iso R (Fin.append s t)).hom).injective
  have hcycle (x : R) := ConcreteCategory.congr_hom
    (OrientedTopCohomology.cycleClass_iso R (Fin.append s t))
      ((OrientedTopCohomology.evaluation R (Fin.append s t)).symm x)
  have hx (x : R) : (OrientedTopCohomology.iso R (Fin.append s t)).hom
      (TopHomologyCokernel.cycleClass _ (c+m)
        (OrientedTopCohomology.outgoing_isZero R (Fin.append s t))
          ((OrientedTopCohomology.evaluation R (Fin.append s t)).symm x)) =
      Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) x :=
    (hcycle x).trans (congrArg (Ideal.Quotient.mk _)
      ((OrientedTopCohomology.evaluation R (Fin.append s t)).apply_symm_apply x))
  exact (hx a).trans (h.trans (hx b).symm)

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

theorem weighted_eq (a b : R)
    (h : Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) a =
      Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) b) :
    a • KoszulPartial.PartialClass.supportedClass R P U s t ht (KoszulPartial.TopResidue.functional R) =
      b • KoszulPartial.PartialClass.supportedClass R P U s t ht (KoszulPartial.TopResidue.functional R) := by
  rw [← ScalarPartialClass.supportedClass_smul,
    ← ScalarPartialClass.supportedClass_smul,
    ← functional_eq R s t a, ← functional_eq R s t b]
  rw [KoszulPartial.PartialClass.supportedClass_eq, KoszulPartial.PartialClass.supportedClass_eq,
    sourceClass_eq R s t a b h]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FractionQuotient
