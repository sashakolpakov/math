import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFactor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Affinization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FieldGeometricConnectedness
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ZeroDimensionalFlat

/-! # Geometric Connectedness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.GeometricConnectedness

noncomputable section

/-! The actual map to global functions has geometrically connected fibers for a smooth proper projective scheme over a finite field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Finite k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X

omit [Finite k] [Smooth X.hom] in
theorem proper : IsProper (WittFactor.affinization k X) :=
  AlgebraicGeometry.FormalGeometry.Completion.Proper.Affinization.Construction.proper_toSpecΓ X.hom

include hprojective in
theorem geometricallyConnected : GeometricallyConnected (WittFactor.affinization k X) := by
  let Y := Spec (CommRingCat.of A)
  let g : X.left ⟶ Y := WittFactor.affinization k X
  let : IsProper g := proper k X
  let : IsIso g.appTop := by
    change IsIso X.left.toSpecΓ.appTop
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  let : Finite A := SmoothProper.GlobalFunctionAlgebra.finite k X hprojective
  let : Finite Γ(Y, ⊤) := Finite.of_injective (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).injective
  let : IsArtinianRing Γ(Y, ⊤) := isArtinian_of_finite
  let : Ring.KrullDimLE 0 Γ(Y, ⊤) := inferInstance
  let : _root_.IsReduced A := SmoothProper.GlobalFunctionAlgebra.reduced k X
  let : IsReduced Y := inferInstance
  let : _root_.IsReduced Γ(Y, ⊤) := inferInstance
  constructor
  intro L _ t Z fst snd H
  let : Flat t := AlgebraicGeometry.FormalGeometry.Completion.ZeroDimensionalFlat.Construction.schemeMap_flat_of_reduced_zeroDimensional_affine t
  let : GeometricallyConnected (pullback.snd g t) :=
    AlgebraicGeometry.FormalGeometry.Completion.Proper.FieldGeometricConnectedness.Construction.proper_flat_field_baseChange_geometricallyConnected g L t
  let : ConnectedSpace ↥(pullback g t : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd g t)
  exact H.isoPullback.symm.hom.homeomorph.connectedSpace_iff.mp inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.GeometricConnectedness
