import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothStalkDomains
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeDomainComponents
import OAI.AlgebraicGeometry.FormalGeometry.Completion.DisjointNoetherianComponents
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FiberComponents

/-! # Smooth Integral Components -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothIntegralComponents.Construction

noncomputable section

/-!
# Completion: integral connected components of smooth Noetherian schemes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Domain stalks make each connected component of a Noetherian scheme integral. -/
theorem noetherian_domain_stalk_component_isIntegral (X : Scheme.{u}) [IsNoetherian X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] (x : X) :
    IsIntegral (Proper.FiberComponents.Construction.noetherianComponentOpen X x).toScheme := by
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IrreducibleSpace (Proper.FiberComponents.Construction.noetherianComponentOpen X x).toScheme :=
    isIrreducible_iff_irreducibleSpace.mp
      (DisjointNoetherianComponents.Construction.disjoint_noetherian_connectedComponent_isIrreducible X
        (fun y => SchemeDomainComponents.Construction.scheme_components_eq_of_domain_stalk X y) x)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The actual connected component of a smooth Noetherian scheme over a field is integral. -/
theorem smooth_noetherian_component_isIntegral (K : Type u) [Field K]
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] (x : X) :
    IsIntegral (Proper.FiberComponents.Construction.noetherianComponentOpen X x).toScheme := by
  have (y : X) : IsDomain (X.presheaf.stalk y) := SmoothStalkDomains.Construction.smooth_field_stalk_isDomain K f y
  exact noetherian_domain_stalk_component_isIntegral X x

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothIntegralComponents.Construction
