import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Map

/-! # Hom Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.HomCoordinates

noncomputable section

/-! Coordinate isomorphisms connecting ordinary Hom of the product
point Koszul resolution to the standard concatenated-equation Hom
complex, preserving the actual normal inclusion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (s : Fin c → R) (t : Fin m → R)

abbrev normalIso := Koszul.HomCoefficientComplex.iso R (Fin c → R) (KoszulPartial.Fractions.modules R P)
  (Koszul.GeneratorMatrix.equation R s)

def pointIso : HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P)
    (Exterior.KoszulComplex.complex R (KoszulPartial.Fractions.ambient R (c := c) (m := m))
      (KoszulPartial.Differential.equation R s t)) ≅ KoszulPartial.Components.coefficient R P (Fin.append s t) :=
  ((HomCoefficientFunctor.functor R (KoszulPartial.Fractions.modules R P)).mapHomologicalComplex (.up ℕ)).mapIso
    ((HomologicalComplex.opFunctor (ModuleCat R) (.down ℕ)).mapIso
      (Koszul.DuplicateFraction.pointIso R s t).op) ≪≫
    Koszul.HomCoefficientComplex.iso R (Fin (c + m) → R) (KoszulPartial.Fractions.modules R P)
      (Koszul.GeneratorMatrix.equation R (Fin.append s t))

omit [HasFiniteProducts C] in
theorem square : (pointIso R P s t).hom ≫ Koszul.DuplicateFraction.normalMap R s t P =
    HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) (KoszulPartial.Resolution.inclusion R s t) ≫
      (normalIso R P s).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change (⋀[R]^q (KoszulPartial.Fractions.ambient R (c := c) (m := m))) →ₗ[R] P.obj a at φ
  change (⋀[R]^q (Fin c → R)) at x
  change φ ((Koszul.DuplicateFraction.pointIso R s t).hom.f q
      ((Koszul.DuplicateFraction.normalInclusion R s t).f q x)) =
    φ ((KoszulPartial.Resolution.inclusion R s t).f q x)
  have he := congrArg (fun f => (f.f q).hom)
    (Koszul.DuplicateFraction.normalInclusion_pointIso R s t)
  exact congrArg φ (LinearMap.congr_fun he x)

variable {L K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (eP : HomotopyEquiv L (HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P)
    (Exterior.KoszulComplex.complex R (KoszulPartial.Fractions.ambient R (c := c) (m := m))
      (KoszulPartial.Differential.equation R s t))))
  (eN : HomotopyEquiv K (HomCoefficientFunctor.complex R (KoszulPartial.Fractions.modules R P)
    (Koszul.OrientedTopCohomology.koszul R s)))
  (r : L ⟶ K)
  (h : Homotopy (r ≫ eN.hom) (eP.hom ≫ HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P)
    (KoszulPartial.Resolution.inclusion R s t)))

def homotopy : Homotopy
    (r ≫ (eN.trans (HomotopyEquiv.ofIso (normalIso R P s))).hom)
    ((eP.trans (HomotopyEquiv.ofIso (pointIso R P s t))).hom ≫
      Koszul.DuplicateFraction.normalMap R s t P) := by
  change Homotopy (r ≫ (eN.hom ≫ (normalIso R P s).hom))
    ((eP.hom ≫ (pointIso R P s t).hom) ≫ Koszul.DuplicateFraction.normalMap R s t P)
  exact (Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    ((h.compRight (normalIso R P s).hom).trans
      (Homotopy.ofEq (by rw [Category.assoc, ← square, ← Category.assoc])))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.HomCoordinates
