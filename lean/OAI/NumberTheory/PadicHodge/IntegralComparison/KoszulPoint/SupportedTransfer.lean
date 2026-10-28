import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechHomotopy

/-! # Supported Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedTransfer

noncomputable section

/-! Transport the explicit point-supported lift to any actual Hom
resolution, retaining its normalization after passing to a surviving
coefficient complex. -/
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
  {L T : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (e : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))

def lift := SupportedLift.map R s t P U ht e.inv

@[reassoc]
theorem forget : lift R P U s t ht e ≫ AugmentedOrdered.CechForget.forgetSupport U L =
    KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t) ≫ AugmentedOrdered.CechForgetNaturality.ambientMap e.inv :=
  SupportedLift.map_forget R s t P U ht e.inv

variable (b : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶ T)

theorem residue (q : ℕ) :
    homologyMap (lift R P U s t ht e ≫ AugmentedOrdered.CechForgetNaturality.map U (e.hom ≫ b)) q =
      homologyMap (SupportedLift.map R s t P U ht b) q := by
  have he := AugmentedOrdered.CechHomotopy.homology U
    (e.homotopyInvHomId.compRightId b) q
  change homologyMap (AugmentedOrdered.CechForgetNaturality.map U (e.inv ≫ (e.hom ≫ b))) q = homologyMap (AugmentedOrdered.CechForgetNaturality.map U b) q at he
  have hc : homologyMap (AugmentedOrdered.CechForgetNaturality.map U (e.inv ≫ (e.hom ≫ b))) q =
      homologyMap (AugmentedOrdered.CechForgetNaturality.map U e.inv) q ≫ homologyMap (AugmentedOrdered.CechForgetNaturality.map U (e.hom ≫ b)) q :=
    AugmentedOrdered.CechHomotopy.homology_comp U e.inv (e.hom ≫ b) q
  rw [hc] at he
  dsimp only [lift, SupportedLift.map]
  simp only [homologyMap_comp]
  rw [Category.assoc, he]

theorem residue_forget (q : ℕ) :
    homologyMap (lift R P U s t ht e ≫ AugmentedOrdered.CechForgetNaturality.map U (e.hom ≫ b)) q ≫
      homologyMap (AugmentedOrdered.CechForget.forgetSupport U T) q =
        homologyMap (KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t)) q ≫
          homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap b) q := by
  rw [residue]
  exact SupportedLift.homology_forget R s t P U ht b q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedTransfer
