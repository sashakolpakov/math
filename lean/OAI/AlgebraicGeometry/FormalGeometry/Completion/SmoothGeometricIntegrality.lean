import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ReducedFieldNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothToNormalization
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Smooth Geometric Integrality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothGeometricIntegrality.Construction

noncomputable section

/-!
# Completion: geometric integrality of the proved normalization fibers

A connected smooth proper field scheme is integral: its domain stalks
separate its irreducible components. Consequently, geometric connectedness
of a proper smooth morphism gives geometric integrality. This applies to
all normalization fibers over a field and to flat field-valued base changes
of the proper smooth families under consideration.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- A connected smooth proper scheme over a field is integral. -/
theorem smooth_proper_connected_field_isIntegral (K : Type u) [Field K]
    {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [Smooth f] : IsIntegral X := by
  have : IsNoetherian X := Proper.FiberComponents.Construction.properField_isNoetherian K f
  have (x : X) : IsDomain (X.presheaf.stalk x) := SmoothStalkDomains.Construction.smooth_field_stalk_isDomain K f x
  have : IsReduced X := isReduced_of_isReduced_stalk X
  let x : X := Nonempty.some inferInstance
  have h := DisjointNoetherianComponents.Construction.disjoint_noetherian_connectedComponent_isIrreducible X
    (fun y => SchemeDomainComponents.Construction.scheme_components_eq_of_domain_stalk X y) x
  rw [PreconnectedSpace.connectedComponent_eq_univ x] at h
  have : IrreducibleSpace X := by rwa [irreducibleSpace_def]
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- For a proper smooth morphism, geometrically connected fibers are geometrically integral. -/
theorem proper_smooth_geometricallyIntegral_of_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  constructor
  intro K _ g Z fst snd H
  have : IsProper snd := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) H inferInstance
  have : ConnectedSpace Z :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) g fst snd H
  exact smooth_proper_connected_field_isIntegral K snd

/-- Over a field, the actual first normalization factor of a smooth proper scheme has
geometrically integral fibers. -/
theorem proper_smooth_field_toNormalization_geometricallyIntegral
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [Smooth f] :
    GeometricallyIntegral f.toNormalization := by
  have (x : X) : IsDomain (X.presheaf.stalk x) := SmoothStalkDomains.Construction.smooth_field_stalk_isDomain K f x
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsProper f.toNormalization := Proper.Normalization.Construction.proper_toNormalization f
  have : Smooth f.toNormalization := Proper.SmoothToNormalization.Construction.proper_smooth_family_toNormalization_smooth K f f
  have : GeometricallyConnected f.toNormalization :=
    Proper.ReducedFieldNormalization.Construction.proper_reduced_field_toNormalization_geometricallyConnected K f
  exact proper_smooth_geometricallyIntegral_of_geometricallyConnected f.toNormalization

/-- Flat field-valued base changes of the actual proper smooth normalization map have
geometrically integral fibers. -/
theorem proper_smooth_toNormalization_flat_field_baseChange_geometricallyIntegral
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsAffine Y]
    (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (f : X ⟶ Y) [IsProper f] [Smooth f]
    (L : Type u) [Field L] (g : Spec (CommRingCat.of L) ⟶ f.normalization) [Flat g] :
    GeometricallyIntegral (pullback.snd f.toNormalization g) := by
  have : IsProper f.toNormalization := Proper.Normalization.Construction.proper_toNormalization f
  have : Smooth f.toNormalization := Proper.SmoothToNormalization.Construction.proper_smooth_family_toNormalization_smooth K pX f
  have : GeometricallyConnected (pullback.snd f.toNormalization g) :=
    Proper.FieldGeometricConnectedness.Construction.proper_toNormalization_flat_field_baseChange_geometricallyConnected f L g
  exact proper_smooth_geometricallyIntegral_of_geometricallyConnected
    (pullback.snd f.toNormalization g)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothGeometricIntegrality.Construction
