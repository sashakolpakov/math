import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalDomainConnected
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FlatSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Field Geometric Connectedness -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FieldGeometricConnectedness.Construction

noncomputable section

/-!
# Completion: geometric connectedness from actual proper global functions

Over a field, flat base change preserves the structural isomorphism on
global functions. Every field base change therefore has a global function
domain and is connected as an actual scheme.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- A proper field scheme with only the base field as global functions is geometrically connected. -/
theorem proper_field_geometricallyConnected_of_appTop_isIso (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsIso f.appTop] :
    GeometricallyConnected f := by
  constructor
  intro L _ g Z fst snd H
  have : IsIso (pullback.snd f g).appTop :=
    (FlatSections.Construction.proper_flat_affine_sections_isPushout f g).isIso_inr_of_isIso
  let e : Γ(pullback f g, ⊤) ≅ CommRingCat.of L :=
    (asIso (pullback.snd f g).appTop).symm ≪≫ Scheme.ΓSpecIso _
  have : IsDomain Γ(pullback f g, ⊤) := e.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have : ConnectedSpace (pullback f g : Scheme.{u}) := GlobalDomainConnected.Construction.scheme_connected_of_globalFunctionDomain _
  exact H.isoPullback.symm.hom.homeomorph.connectedSpace_iff.mp inferInstance

theorem proper_flat_field_baseChange_geometricallyConnected {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] [IsIso f.appTop]
    (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ Y) [Flat g] :
    GeometricallyConnected (pullback.snd f g) := by
  have : IsIso (pullback.snd f g).appTop :=
    (FlatSections.Construction.proper_flat_affine_sections_isPushout f g).isIso_inr_of_isIso
  exact proper_field_geometricallyConnected_of_appTop_isIso K (pullback.snd f g)

/-- The actual map to normalization has geometrically connected flat field-valued base changes. -/
theorem proper_toNormalization_flat_field_baseChange_geometricallyConnected
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f]
    (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ f.normalization) [Flat g] :
    GeometricallyConnected (pullback.snd f.toNormalization g) := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have : IsProper f.toNormalization := Normalization.Construction.proper_toNormalization f
  have : IsIso f.toNormalization.appTop := Normalization.Construction.proper_toNormalization_appTop_isIso f
  exact proper_flat_field_baseChange_geometricallyConnected f.toNormalization K g

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FieldGeometricConnectedness.Construction
