import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsConnectedness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.GlobalFunctionsPushout
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Global Functions Connectedness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GlobalFunctionsConnectedness

noncomputable section

/-! For a pointed proper smooth scheme over a field, geometric connectedness is equivalent to its structure map inducing an isomorphism on global functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem field_connected_of_globalFunctionsIso {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsIso p.appTop] (x : Spec (.of K) ⟶ X) : ConnectedSpace X := by
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)).toField
  have : IsDomain Γ(X, ⊤) := (asIso p.appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have : Nonempty X := ⟨x (Nonempty.some (inferInstance : Nonempty (Spec (.of K))))⟩
  exact Global.FunctionsConnectedness.scheme_connected_of_globalSections_domain X

theorem properField_affineBaseChange_globalFunctionsIso_of_iso
    {K : Type u} [Field K] {X Y Z : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p] [IsIso p.appTop]
    {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ Spec (.of K)} (h : IsPullback a b p c) [IsAffine Y] : IsIso b.appTop := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have hp : IsSeparated (p ≫ terminal.from (Spec (.of K))) := inferInstance
  have : IsSeparated (terminal.from X) := (terminal.comp_from p) ▸ hp
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)).toField
  have : Module.Flat Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra c) := inferInstance
  exact HilbertConstruction.Flat.GlobalFunctionsPushout.flatBaseChange_globalFunctions_isIso h

theorem properField_geometricallyConnected_of_globalFunctionsIso
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p] [IsIso p.appTop]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) : GeometricallyConnected p := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ c => ?_⟩
  have : IsIso (pullback.snd p c).appTop :=
    properField_affineBaseChange_globalFunctionsIso_of_iso p (IsPullback.of_hasPullback p c)
  let y : Spec (.of L) ⟶ pullback p c := pullback.lift (c ≫ x) (𝟙 _) (by rw [Category.assoc, hx]; simp)
  exact field_connected_of_globalFunctionsIso (pullback.snd p c) y

theorem properSmoothPointed_geometricallyConnected_iff_globalFunctionsIso
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p] [Smooth p]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) : GeometricallyConnected p ↔ IsIso p.appTop := by
  constructor
  · intro h
    let : GeometricallyConnected p := h
    have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton p
    have : IsReduced X := HilbertConstruction.Smooth.ReducedFibers.smoothOverField_isReduced p
    exact (Proper.ConnectedReducedConstants.properConnectedReducedPointGlobalIso p x hx).isIso_hom
  · intro h
    let : IsIso p.appTop := h
    exact properField_geometricallyConnected_of_globalFunctionsIso p x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GlobalFunctionsConnectedness
