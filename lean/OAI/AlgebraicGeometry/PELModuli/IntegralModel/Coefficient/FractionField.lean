import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Localization.FractionRing

/-! # Fraction Field -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient

noncomputable section

/-! Factor the ambient field point of a finite coefficient model through
the actual fraction field of its coefficient ring. The latter inclusion is
a localization, while the remaining field extension is faithfully flat. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R K : Type) [CommRing R] [Field K] [Algebra R K] (s : Finset K)

abbrev FractionField.Coefficients.coefficientFractionField := FractionRing (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s)

def FractionField.Coefficients.coefficientFieldEmbedding : FractionField.Coefficients.coefficientFractionField R K s →+* K :=
  IsFractionRing.lift (K := FractionField.Coefficients.coefficientFractionField R K s)
    (g := (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s).val.toRingHom) Subtype.val_injective

theorem FractionField.Coefficients.coefficientFieldEmbedding_comp :
    (FractionField.Coefficients.coefficientFieldEmbedding R K s).comp
      (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (FractionField.Coefficients.coefficientFractionField R K s)) =
        (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s).val.toRingHom := by
  ext a
  exact IsFractionRing.lift_algebraMap Subtype.val_injective a

def FractionField.Coefficients.fractionBaseMap : Spec (.of (FractionField.Coefficients.coefficientFractionField R K s)) ⟶ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s :=
  Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (FractionField.Coefficients.coefficientFractionField R K s)))

def FractionField.Coefficients.ambientFieldMap : Spec (.of K) ⟶ Spec (.of (FractionField.Coefficients.coefficientFractionField R K s)) :=
  Spec.map (CommRingCat.ofHom (FractionField.Coefficients.coefficientFieldEmbedding R K s))

theorem FractionField.Coefficients.fractionBase_factorization :
    FractionField.Coefficients.ambientFieldMap R K s ≫ FractionField.Coefficients.fractionBaseMap R K s = ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s := by
  change Spec.map (CommRingCat.ofHom (FractionField.Coefficients.coefficientFieldEmbedding R K s)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (FractionField.Coefficients.coefficientFractionField R K s))) = _
  rw [← Spec.map_comp]
  exact congrArg (fun a => Spec.map (CommRingCat.ofHom a)) (FractionField.Coefficients.coefficientFieldEmbedding_comp R K s)

instance FractionField.Coefficients.fractionBaseMap_preimmersion : IsPreimmersion (FractionField.Coefficients.fractionBaseMap R K s) :=
  IsPreimmersion.of_isLocalization (nonZeroDivisors (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s))

instance FractionField.Coefficients.ambientFieldMap_flat : Flat (FractionField.Coefficients.ambientFieldMap R K s) := inferInstance

instance FractionField.Coefficients.ambientFieldMap_surjective : Surjective (FractionField.Coefficients.ambientFieldMap R K s) :=
  ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ x⟩⟩

instance FractionField.Coefficients.ambientFieldMap_quasiCompact : QuasiCompact (FractionField.Coefficients.ambientFieldMap R K s) := by
  unfold FractionField.Coefficients.ambientFieldMap
  infer_instance

variable {R K} {X : Over (Spec (.of K))}

def Models.Coefficients.CoefficientModel.fractionFiberIso (M : Models.Coefficients.CoefficientModel R K X) :
    (Over.pullback (FractionField.Coefficients.ambientFieldMap R K M.coefficients)).obj
        ((Over.pullback (FractionField.Coefficients.fractionBaseMap R K M.coefficients)).obj M.model) ≅ X :=
  Group.BaseChangeComparisons.GroupBaseChange.iteratedIso M.model (FractionField.Coefficients.fractionBaseMap R K M.coefficients)
    (FractionField.Coefficients.ambientFieldMap R K M.coefficients) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K M.coefficients)
    (FractionField.Coefficients.fractionBase_factorization R K M.coefficients) ≪≫ M.genericIso

theorem Models.Coefficients.CoefficientModel.smooth_fractionFiber (M : Models.Coefficients.CoefficientModel R K X)
    [Smooth X.hom] :
    Smooth ((Over.pullback (FractionField.Coefficients.fractionBaseMap R K M.coefficients)).obj M.model).hom := by
  let Y := (Over.pullback (FractionField.Coefficients.fractionBaseMap R K M.coefficients)).obj M.model
  let ψ := FractionField.Coefficients.ambientFieldMap R K M.coefficients
  let e := M.fractionFiberIso
  have : IsIso e.hom.left := ((Over.forget (Spec (.of K))).mapIso e).isIso_hom
  have hsm : Smooth (((Over.pullback ψ).obj Y).hom) := by
    rw [← e.hom.w]
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback Y.hom ψ).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient
