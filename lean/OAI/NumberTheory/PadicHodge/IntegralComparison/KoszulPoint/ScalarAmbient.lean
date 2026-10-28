import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarCoordinates

/-! # Scalar Ambient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarAmbient

noncomputable section

/-! The scalar of a supported point class is computed by its ordinary
ambient Ext coordinate. This removes all choices of support cover from
the scalar calculation. -/
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
  {n : ℕ} (a : Fin n → R)
  {L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (e : HomotopyEquiv L (KoszulPartial.Components.coefficient R P a))

def coordinate : (AugmentedOrdered.CechForget.ambientComplex L).homology n ⟶
    ModuleCat.of R (R ⧸ Koszul.OrientedTopCohomology.ideal R a) := by
  letI := Koszul.TerminalScalars.isIso R P a hP
  exact homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap e.hom) n ≫
    (homologyMapIso (asIso (KoszulPartial.CanonicalMap.scalarsMap R P a)) n).inv ≫
      (Koszul.OrientedTopCohomology.iso R a).hom

variable (e' : HomotopyEquiv L (KoszulPartial.Components.coefficient R P a))
  (h : Homotopy e.hom e'.hom)

include h in
theorem coordinate_homotopy : coordinate R P hP a e = coordinate R P hP a e' := by
  let F := (CategoryTheory.evaluation Cᵒᵖ (ModuleCat R)).obj (op (⊤_ C))
  have he : homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap e.hom) n = homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap e'.hom) n :=
    (F.mapHomotopy h).homologyMap_eq n
  unfold coordinate
  rw [he]

theorem scalar (k : Type u) [CommRing k] [Algebra k R]
    {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
    (e : HomotopyEquiv L (KoszulPartial.Components.coefficient R P (Fin.append s t)))
    (d : ℕ) (hL : ∀ q, q ≠ d → L.ExactAt q)
    (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) q,
      IsZero ((((single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) d).obj (L.homology d)).X p).obj
        (op ((AugmentedOrdered.Cech.formal U q).obj a))))
    (e₀ : (R ⧸ Koszul.OrientedTopCohomology.ideal R (Fin.append s t)) ≃ₐ[k] k)
    (y : ((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).homology (c+m)) :
    ScalarCoordinates.scalar k R P hP U s t e d hL hzero e₀ y =
      e₀ (coordinate R P hP (Fin.append s t) e
        (homologyMap (AugmentedOrdered.CechForget.forgetSupport U L) (c+m) y)) := by
  change e₀ ((Koszul.OrientedTopCohomology.iso R (Fin.append s t)).hom
    ((SupportedIso.ambientIso R P hP s t e (c+m)).inv
      ((Supported.PureForget.iso U L d hL hzero (c+m)).hom y))) = _
  rw [Supported.PureForget.iso_hom]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarAmbient
