import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.HomCoordinates

/-! # Normal Hom Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalHomCoordinates

noncomputable section

/-! Identity normal-Koszul comparison on a common-refinement left leg
remains the literal identity after passing to exterior Hom coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c : ℕ} (s : Fin c → R)

omit [HasFiniteProducts C] in
theorem map_id : HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P)
    (𝟙 (OrientedTopCohomology.koszul R s)) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext a
  rfl

variable {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eK : HomotopyEquiv K (HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P)
    (OrientedTopCohomology.koszul R s)))
  (eL : HomotopyEquiv L (HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P)
    (OrientedTopCohomology.koszul R s)))
  (a : K ⟶ L)
  (h : Homotopy (a ≫ eL.hom) (eK.hom ≫ HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P)
    (𝟙 (OrientedTopCohomology.koszul R s))))

def homotopy : Homotopy
    (a ≫ (eL.trans (HomotopyEquiv.ofIso (KoszulPoint.HomCoordinates.normalIso R P s))).hom)
    (eK.trans (HomotopyEquiv.ofIso (KoszulPoint.HomCoordinates.normalIso R P s))).hom := by
  have h' : Homotopy (a ≫ eL.hom) eK.hom := by
    simpa only [map_id, Category.comp_id] using h
  exact (Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    (h'.compRight (KoszulPoint.HomCoordinates.normalIso R P s).hom)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalHomCoordinates
