import OAI.AlgebraicGeometry.FormalGeometry.Completion.NoetherianComponents
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ConnectedField

/-! # Fiber Components -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FiberComponents.Construction

noncomputable section

/-!
# Completion: actual connected components of proper geometric fibers

The components are open and closed subschemes, remain proper and reduced,
and have only constant global functions over an algebraically closed field.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- A connected component as an actual open subscheme of a Noetherian scheme. -/
def noetherianComponentOpen (X : Scheme.{u}) [IsNoetherian X] (x : X) : X.Opens :=
  ⟨connectedComponent x, (NoetherianComponents.Construction.noetherian_connectedComponent_isClopen X x).isOpen⟩

instance noetherianComponentOpen_connected (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    ConnectedSpace (noetherianComponentOpen X x).toScheme :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

instance noetherianComponentOpen_ι_isClosedImmersion (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    IsClosedImmersion (noetherianComponentOpen X x).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact isClosed_connectedComponent

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

include f

/-- The finite-type proper fiber is a Noetherian scheme. -/
theorem properField_isNoetherian : IsNoetherian X := {
  __ := LocallyOfFiniteType.isLocallyNoetherian f
  __ := QuasiCompact.compactSpace_of_compactSpace f }

/-- Every connected component of a reduced proper geometric fiber has exactly the base field
as its global functions, using the actual restriction of the structure map. -/
theorem proper_geometric_component_appTop_isIso [IsAlgClosed K] [IsReduced X] (x : X) :
    letI := properField_isNoetherian K f
    IsIso ((noetherianComponentOpen X x).ι ≫ f).appTop := by
  let := properField_isNoetherian K f
  exact ConnectedField.Construction.proper_connected_reduced_appTop_isIso K ((noetherianComponentOpen X x).ι ≫ f)

/-- The actual normalization of each connected geometric component is the geometric point. -/
theorem proper_geometric_component_fromNormalization_isIso
    [IsAlgClosed K] [IsReduced X] (x : X) :
    letI := properField_isNoetherian K f
    IsIso ((noetherianComponentOpen X x).ι ≫ f).fromNormalization := by
  let := properField_isNoetherian K f
  have := proper_geometric_component_appTop_isIso K f x
  exact Normalization.Construction.proper_fromNormalization_isIso_of_appTop ((noetherianComponentOpen X x).ι ≫ f)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FiberComponents.Construction
