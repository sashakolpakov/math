import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalHomCoordinates

/-! # Refined Point Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedPointCoordinates

noncomputable section

/-! Bundled normalization of both common-refinement legs: the inverse
used in the point class inverts the actual left map, and the complete
zigzag has the literal mixed-fraction coordinate. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  {L K F : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
  (eN : HomotopyEquiv K (KoszulPartial.Components.coefficient R P s))
  (eF : HomotopyEquiv F (KoszulPartial.Components.coefficient R P s)) (r : L ⟶ K) (l : F ⟶ K)
  (hr : Homotopy (r ≫ eN.hom) (eP.hom ≫ DuplicateFraction.normalMap R s t P))
  (hl : Homotopy (l ≫ eN.hom) eF.hom)

abbrev comparison (q : ℕ) := And.intro
  (Supported.CechHomotopyEquivalence.refinementIso_hom U eF eN l hl q)
  (RefinedPointFraction.coordinates R P U s t ht eP eN eF r hr q)

abbrev class_eq (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) := And.intro
  (Supported.CechHomotopyEquivalence.refinementIso_hom U eF eN l hl (c + m))
  (RefinedPointFraction.class_eq R P U s t ht eP eN eF r hr φ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.RefinedPointCoordinates
