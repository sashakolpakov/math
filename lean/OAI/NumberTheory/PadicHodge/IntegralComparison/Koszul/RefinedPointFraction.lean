import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Map
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence

/-! # Refined Point Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedPointFraction

noncomputable section

/-! The entire supported common-refinement zigzag has the canonical
mixed-fraction coordinate: right leg followed by the genuine inverse
of the left leg, in the original fixed-resolution cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  {L K F : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (eN : HomotopyEquiv K (KoszulPartial.Components.coefficient R P s))
  (eF : HomotopyEquiv F (KoszulPartial.Components.coefficient R P s)) (r : L ⟶ K)
  (h : Homotopy (r ≫ eN.hom) (eP.hom ≫ DuplicateFraction.normalMap R s t P))

def map (q : ℕ) : (KoszulPartial.Components.source R s t).homology q ⟶ (Supported.CechHomotopyEquivalence.functor U q).obj F :=
  homologyMap (DualComplexHomology.map R (DuplicateFraction.pointIso R s t).hom ≫
    KoszulPoint.SupportedLift.lift R s t P U ht) q ≫
      (Supported.CechHomotopyEquivalence.iso U eP q).inv ≫ (Supported.CechHomotopyEquivalence.functor U q).map r ≫ (Supported.CechHomotopyEquivalence.refinementIso U eF eN q).inv

include h in
theorem coordinates (q : ℕ) : RefinedPointFraction.map R P U s t ht eP eN eF r q ≫ (Supported.CechHomotopyEquivalence.iso U eF q).hom =
    homologyMap (KoszulPartial.Total.map R P U s t ht) q := by
  dsimp only [RefinedPointFraction.map]
  simp only [Category.assoc]
  rw [Supported.CechHomotopyEquivalence.refinementIso_inv_coordinates]
  have he : (Supported.CechHomotopyEquivalence.iso U eP q).inv ≫ (Supported.CechHomotopyEquivalence.functor U q).map r ≫ (Supported.CechHomotopyEquivalence.iso U eN q).hom =
      (Supported.CechHomotopyEquivalence.functor U q).map (eP.inv ≫ (r ≫ eN.hom)) := by
    change (Supported.CechHomotopyEquivalence.functor U q).map eP.inv ≫ (Supported.CechHomotopyEquivalence.functor U q).map r ≫ (Supported.CechHomotopyEquivalence.functor U q).map eN.hom = _
    rw [Functor.map_comp, Functor.map_comp]
  rw [he]
  have hm : (Supported.CechHomotopyEquivalence.functor U q).map (eP.inv ≫ (r ≫ eN.hom)) =
      homologyMap (AugmentedOrdered.CechForgetNaturality.map U (eP.inv ≫ (r ≫ eN.hom))) q := rfl
  rw [hm]
  simpa only [KoszulPoint.Map.Comparison.supportedMap, homologyMap_comp, Category.assoc] using
    KoszulPoint.Map.Comparison.homology R P U s t ht eP eN r h q

include h in
theorem class_eq (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    (Supported.CechHomotopyEquivalence.iso U eF (c + m)).hom
      (RefinedPointFraction.map R P U s t ht eP eN eF r (c + m) (KoszulPartial.PartialClass.sourceClass R s t φ)) =
        KoszulPartial.PartialClass.supportedClass R P U s t ht φ := by
  have hh := ConcreteCategory.congr_hom (coordinates R P U s t ht eP eN eF r h (c + m))
    (KoszulPartial.PartialClass.sourceClass R s t φ)
  exact hh.trans (KoszulPartial.PartialClass.supportedClass_eq R P U s t ht φ).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedPointFraction
