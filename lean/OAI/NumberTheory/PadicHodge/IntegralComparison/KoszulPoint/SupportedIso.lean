import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TerminalScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PureForget

/-! # Supported Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedIso

noncomputable section

/-! The duplicate-parameter construction gives the unique supported
lift of every class of the original dual resolution. Its isomorphism
uses the literal scalar map and original support-forgetting map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  (hP : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  {L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (e : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))

def ambientIso (q : ℕ) :
    (DualComplexHomology.complex R
      (Koszul.OrientedTopCohomology.koszul R (Fin.append s t))).homology q ≅
        (Supported.ConcentrationForget.ambientFunctor q).obj L := by
  letI := Koszul.TerminalScalars.isIso R P (Fin.append s t) hP
  let F := (CategoryTheory.evaluation Cᵒᵖ (ModuleCat R)).obj (op (⊤_ C))
  exact homologyMapIso (asIso (KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t))) q ≪≫
    ((F.mapHomotopyEquiv e).toHomologyIso q).symm

theorem ambientIso_hom (q : ℕ) : (ambientIso R P hP s t e q).hom =
    homologyMap (KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t)) q ≫
      homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap e.inv) q := rfl

variable (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
  (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
    IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))

def iso (q : ℕ) := ambientIso R P hP s t e q ≪≫
  (Supported.PureForget.iso U L d hL hzero q).symm

theorem iso_hom (q : ℕ) : (iso R P hP U s t e d hL hzero q).hom =
    homologyMap (SupportedTransfer.lift R P U s t ht e) q := by
  apply (cancel_mono (Supported.PureForget.iso U L d hL hzero q).hom).mp
  dsimp only [iso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Supported.PureForget.iso_hom, ambientIso_hom]
  have h := congrArg (fun a => homologyMap a q)
    (SupportedTransfer.forget R P U s t ht e)
  simpa only [homologyMap_comp] using h.symm

include ht in
theorem inverse_lift (q : ℕ) :
    (iso R P hP U s t e d hL hzero q).inv ≫
      homologyMap (SupportedTransfer.lift R P U s t ht e) q = 𝟙 _ := by
  rw [← iso_hom R P hP U s t ht e d hL hzero q]
  exact Iso.inv_hom_id _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedIso
