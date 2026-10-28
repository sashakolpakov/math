import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor

/-! # Hom Coefficient Identity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientIdentity.Functor

noncomputable section

open _root_.CategoryTheory Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type v} [Category C] (R : Type u) [CommRing R]
  (P : C ⥤ ModuleCat.{u} R) {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)

theorem map_id : HomCoefficientFunctor.map R P (𝟙 K) = 𝟙 (HomCoefficientFunctor.complex R P K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  rfl

variable {L N : HomologicalComplex (C ⥤ ModuleCat.{u} R) c.symm}
  (eL : HomotopyEquiv L (HomCoefficientFunctor.complex R P K))
  (eN : HomotopyEquiv N (HomCoefficientFunctor.complex R P K)) (a : L ⟶ N)
  (h : Homotopy (a ≫ eN.hom) (eL.hom ≫ HomCoefficientFunctor.map R P (𝟙 K)))

def identityHomotopy : Homotopy (a ≫ eN.hom) eL.hom :=
  h.trans (Homotopy.ofEq (by rw [map_id, Category.comp_id]))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientIdentity.Functor
