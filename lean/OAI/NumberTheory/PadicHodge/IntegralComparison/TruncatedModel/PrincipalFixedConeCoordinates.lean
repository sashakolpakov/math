import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn

/-! # Principal Fixed Cone Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFixedConeCoordinates

noncomputable section

/-! On principal opens the original diagonal cone is the inverse
of restriction from the fixed native crystalline frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_coordinates {C : Type*} [Category C] {K L M : C}
    (a : K ⟶ L) [IsIso a] (e : L ≅ M) (c : K ⟶ M) [IsIso c] (b : M ⟶ K)
    (hc : a ≫ e.hom = c) (hb : b = inv c) : e.hom ≫ b = inv a := by
  apply (cancel_mono c).1
  simp only [Category.assoc, hb, IsIso.inv_hom_id, Category.comp_id]
  rw [← hc, IsIso.inv_hom_id_assoc]

private structure InverseCoordinateData (C : Type*) [Category C] where
  K : C
  L : C
  M : C
  a : K ⟶ L
  e : L ≅ M
  c : K ⟶ M
  b : M ⟶ K
  a_iso : IsIso a
  c_iso : IsIso c
  hc : a ≫ e.hom = c
  hb : b = @CategoryTheory.inv C _ K M c c_iso

private theorem InverseCoordinateData.coordinates {C : Type*} [Category C]
    (d : InverseCoordinateData C) :
    d.e.hom ≫ d.b = @CategoryTheory.inv C _ d.K d.L d.a d.a_iso := by
  let := d.a_iso
  let := d.c_iso
  exact inverse_coordinates d.a d.e d.c d.b d.hc d.hb

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram.functor X.left U.val U.property
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X Y f hp U
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.opens p k n X Y f U
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.sections w n O
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.diagram w n G
local notation "K" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp) (op U)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.restriction p k n X U
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family.cone w n
  (PrincipalIn.Family.center p k n X Y f hp U)
  (PrincipalIn.Family.cone p k n X Y f hp U)

attribute [local instance] PrincipalIn.FixedCoordinates.globalSeparated

/-- The original inverse frame map, expressed in the target coordinates. -/
def coneInTarget :=
  (PrincipalFrameSections.targetIso p k n X Y f hp U).hom ≫
    PrincipalFrameSections.inverse p k n X Y f hp U

/-- The inverse of the fixed-frame restriction. -/
def inverseRestriction := inv (PrincipalIn.FixedCoordinates.restrictionMap p k n X Y f hp U)

private def coordinatesData :=
  InverseCoordinateData.mk _ _ _
    (PrincipalIn.FixedCoordinates.restrictionMap p k n X Y f hp U)
    (PrincipalFrameSections.targetIso p k n X Y f hp U)
    (PrincipalFrameSections.map p k n X Y f hp U)
    (PrincipalFrameSections.inverse p k n X Y f hp U)
    inferInstance inferInstance
    (PrincipalIn.FixedCoordinates.restriction_coordinates p k n X Y f hp U)
    (PrincipalFrameIso.inverse_eq_inv p k n X Y f hp U)

abbrev cone_coordinates :=
  (InverseCoordinateData.coordinates (coordinatesData p k n X Y f hp U))

abbrev localMap := PrincipalIn.DiagonalCoordinates.diagonal p k n X Y f hp U ≫
  inv (PrincipalIn.FixedCoordinates.restrictionMap p k n X Y f hp U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFixedConeCoordinates
