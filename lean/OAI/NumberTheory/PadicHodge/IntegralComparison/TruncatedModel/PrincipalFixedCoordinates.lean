import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFixedConeCoordinates

/-! # Principal Fixed Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFixedCoordinates

noncomputable section

/-! On principal opens the original diagonal cone is the inverse
of restriction from the fixed native crystalline frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem composite_coordinates {C : Type*} [Category C] {K L M N : C}
    {a : K ⟶ L} {b : L ⟶ M} {c : M ⟶ N} {d : L ⟶ N} {e : K ⟶ M}
    (hi : b ≫ c = d) (hd : a ≫ b = e) : a ≫ d = e ≫ c := by
  rw [← hi, ← Category.assoc, hd]

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

abbrev coordinates :=
  composite_coordinates (PrincipalFixedConeCoordinates.cone_coordinates p k n X Y f hp U)
    (PrincipalIn.DiagonalCoordinates.coordinates p k n X Y f hp U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalFixedCoordinates
