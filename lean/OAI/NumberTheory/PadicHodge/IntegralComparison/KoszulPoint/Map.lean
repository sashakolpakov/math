import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechHomotopy

/-! # Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Map.Comparison

noncomputable section

/-! A genuine native Hom-complex square carries the explicit supported
point lift to the canonical mixed fraction. This is a comparison of
actual cochain maps, retaining any common resolution used by the source. -/
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
  {L K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (eN : HomotopyEquiv K (KoszulPartial.Components.coefficient R P s)) (r : L ⟶ K)
  (h : Homotopy (r ≫ eN.hom)
    (eP.hom ≫ Koszul.DuplicateFraction.normalMap R s t P))

def coefficientHomotopy : Homotopy (eP.inv ≫ (r ≫ eN.hom))
    (Koszul.DuplicateFraction.normalMap R s t P) :=
  (h.compLeft eP.inv).trans
    ((Homotopy.ofEq (Category.assoc _ _ _).symm).trans
      (eP.homotopyInvHomId.compRightId (Koszul.DuplicateFraction.normalMap R s t P)))

def supportedMap : KoszulPartial.Components.source R s t ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ) :=
  DualComplexHomology.map R (Koszul.DuplicateFraction.pointIso R s t).hom ≫
    SupportedLift.lift R s t P U ht ≫ AugmentedOrdered.CechForgetNaturality.map U (eP.inv ≫ (r ≫ eN.hom))

include h in
theorem homology (q : ℕ) : homologyMap (supportedMap R P U s t ht eP eN r) q =
    homologyMap (KoszulPartial.Total.map R P U s t ht) q := by
  have he := AugmentedOrdered.CechHomotopy.homology U
    (coefficientHomotopy R P s t eP eN r h) q
  change homologyMap (AugmentedOrdered.CechForgetNaturality.map U (eP.inv ≫ (r ≫ eN.hom))) q =
    homologyMap (AugmentedOrdered.CechForgetNaturality.map U (Koszul.DuplicateFraction.normalMap R s t P)) q at he
  calc
    _ = homologyMap (Koszul.DuplicateFraction.supportedMap R s t P U ht) q := by
      dsimp only [supportedMap, Koszul.DuplicateFraction.supportedMap,
        SupportedLift.map]
      simp only [homologyMap_comp]
      rw [he]
    _ = _ := Koszul.DuplicateFraction.homology R s t P U ht q

include h in
theorem class_eq (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    homologyMap (supportedMap R P U s t ht eP eN r) (c + m)
      (KoszulPartial.PartialClass.sourceClass R s t φ) =
        KoszulPartial.PartialClass.supportedClass R P U s t ht φ := by
  rw [homology R P U s t ht eP eN r h, KoszulPartial.PartialClass.supportedClass_eq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Map.Comparison
