import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FieldGeometricConnectedness
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ZeroDimensionalFlat

/-! # Reduced Field Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ReducedFieldNormalization.Construction

noncomputable section

/-!
# Completion: geometrically connected normalization fibers over a field

For a reduced proper scheme over a field, the actual relative normalization
is reduced and zero-dimensional. Every morphism into it is therefore flat,
so flat base change of actual global sections settles all geometric fibers.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The coordinate ring of the actual proper field normalization is zero-dimensional. -/
theorem proper_field_normalization_globalFunctions_zeroDimensional
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] :
    Ring.KrullDimLE 0 Γ(f.normalization, ⊤) := by
  have : IsIso f.toNormalization.appTop := Normalization.Construction.proper_toNormalization_appTop_isIso f
  let e := (asIso f.toNormalization.appTop).commRingCatIsoToRingEquiv
  rw [Ring.krullDimLE_iff, ringKrullDim,
    Order.krullDim_eq_of_orderIso (PrimeSpectrum.comapEquiv e),
    ← ringKrullDim, ← Ring.krullDimLE_iff]
  exact ConnectedFunctions.Construction.proper_globalFunctions_krullDimLE_zero K f

/-- All geometric fibers of the actual first normalization factor are connected over a field. -/
theorem proper_reduced_field_toNormalization_geometricallyConnected
    (K : Type u) [Field K] {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] :
    GeometricallyConnected f.toNormalization := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have := proper_field_normalization_globalFunctions_zeroDimensional K f
  constructor
  intro L _ g Z fst snd H
  have : Flat g := ZeroDimensionalFlat.Construction.schemeMap_flat_of_reduced_zeroDimensional_affine g
  have : GeometricallyConnected (pullback.snd f.toNormalization g) :=
    FieldGeometricConnectedness.Construction.proper_toNormalization_flat_field_baseChange_geometricallyConnected f L g
  have : ConnectedSpace (pullback f.toNormalization g : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f.toNormalization g)
  exact H.isoPullback.symm.hom.homeomorph.connectedSpace_iff.mp inferInstance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ReducedFieldNormalization.Construction
