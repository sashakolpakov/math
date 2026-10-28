import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.WeightedSupportedLift
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Supported Coefficient Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedCoefficientEvaluation

noncomputable section

/-! Evaluation of a supported coefficient point class reduces to the
weighted scalar fraction whenever the actual coefficient cochain square
lifts the weighted point quotient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  {L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (a : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶ L) (ev : L ⟶ KoszulPartial.Components.coefficient R P s)

 def supported : KoszulPartial.Components.source R s t ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ) :=
  DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom ≫
    KoszulPoint.SupportedLift.map R s t P U ht a ≫ AugmentedOrdered.CechForgetNaturality.map U ev

 theorem forget : supported R P U s t ht a ev ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) =
    DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom ≫
      KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t) ≫ AugmentedOrdered.CechForgetNaturality.ambientMap (a ≫ ev) := by
  dsimp only [supported]
  rw [Category.assoc, Category.assoc, AugmentedOrdered.CechForgetNaturality.comparison, ← Category.assoc
    (KoszulPoint.SupportedLift.map R s t P U ht a), KoszulPoint.SupportedLift.map_forget]
  simp only [Category.assoc]
  rfl

variable (r : R) (h : Homotopy (a ≫ ev) (r • DuplicateFraction.normalMap R s t P))

 theorem ambient_weight :
    DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom ≫
      KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t) ≫
        AugmentedOrdered.CechForgetNaturality.ambientMap (r • DuplicateFraction.normalMap R s t P) =
      (r • KoszulPartial.Total.map R P U s t ht) ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) := by
  have hs : AugmentedOrdered.CechForgetNaturality.ambientMap (r • DuplicateFraction.normalMap R s t P) =
      r • AugmentedOrdered.CechForgetNaturality.ambientMap (DuplicateFraction.normalMap R s t P) := rfl
  rw [hs, Linear.comp_smul, Linear.comp_smul, Linear.smul_comp]
  apply congrArg (fun x => r • x)
  calc
    _ = DuplicateFraction.supportedMap R s t P U ht ≫
        AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) := by
      dsimp only [DuplicateFraction.supportedMap]
      rw [Category.assoc, KoszulPoint.SupportedLift.map_forget]
    _ = _ := DuplicateFraction.forget R s t P U ht

 def homotopy : Homotopy (supported R P U s t ht a ev)
    (r • KoszulPartial.Total.map R P U s t ht) := by
  let E := (CategoryTheory.evaluation Cᵒᵖ (ModuleCat R)).obj (op (⊤_ C))
  have ha : Homotopy (AugmentedOrdered.CechForgetNaturality.ambientMap (a ≫ ev))
      (AugmentedOrdered.CechForgetNaturality.ambientMap (r • DuplicateFraction.normalMap R s t P)) := E.mapHomotopy h
  apply SupportedUniqueness.homotopy R P U s t ht
  exact (Homotopy.ofEq (forget R P U s t ht a ev)).trans
    ((ha.compLeft (KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t))).compLeft
      (DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom) |>.trans
        (Homotopy.ofEq (ambient_weight R P U s t ht r)))

 include h in
 theorem homology (q : ℕ) : homologyMap (supported R P U s t ht a ev) q =
    r • homologyMap (KoszulPartial.Total.map R P U s t ht) q := by
  rw [← Resolution.CohomologyMaps.homologyMap_smul R]
  exact (homotopy R P U s t ht a ev r h).homologyMap_eq q

 include h in
 theorem class_eq (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    homologyMap (supported R P U s t ht a ev) (c+m)
      (KoszulPartial.PartialClass.sourceClass R s t φ) =
      r • KoszulPartial.PartialClass.supportedClass R P U s t ht φ := by
  have he := ConcreteCategory.congr_hom (homology R P U s t ht a ev r h (c+m))
    (KoszulPartial.PartialClass.sourceClass R s t φ)
  exact he.trans (congrArg (fun z => r • z)
    (KoszulPartial.PartialClass.supportedClass_eq R P U s t ht φ).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedCoefficientEvaluation
