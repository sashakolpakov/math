import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientEvaluationHomotopy

/-! # Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.CoefficientCoordinates

noncomputable section

/-! The standard point coordinates preserve a map into any coefficient
resolution, rather than just the scalar normal resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (s : Fin c → R) (t : Fin m → R)
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (M : ModuleCat.{u} R) (PM : ProjectiveResolution M)
  (a : PM.complex ⟶ (KoszulPartial.Resolution.pointResolution R s t hst).complex)
  {L K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P)
    (KoszulPartial.Resolution.pointResolution R s t hst).complex))
  (eN : HomotopyEquiv K (HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P) PM.complex))
  (r : L ⟶ K)
  (h : Homotopy (r ≫ eN.hom) (eP.hom ≫ HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) a))

def homotopy : Homotopy (r ≫ eN.hom)
    ((eP.trans (HomotopyEquiv.ofIso
      (HomCoordinates.pointIso R P s t))).hom ≫
        Koszul.CoefficientEvaluationHomotopy.pointMap R P s t hst M PM a) :=
  h.trans (Homotopy.ofEq (by
    change eP.hom ≫ HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) a =
      (eP.hom ≫ (HomCoordinates.pointIso R P s t).hom) ≫
        ((HomCoordinates.pointIso R P s t).inv ≫
          HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) a)
    simp only [Category.assoc, Iso.hom_inv_id_assoc]))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.CoefficientCoordinates
