import OAI.AlgebraicGeometry.FormalGeometry.Completion.LocalDomainComponents
import Mathlib.AlgebraicGeometry.Properties

/-! # Scheme Domain Components -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeDomainComponents.Construction

noncomputable section

/-!
# Completion: scheme components are disjoint when their stalks are domains
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Components meeting at a point with a domain stalk must coincide. -/
theorem scheme_components_eq_of_domain_stalk (X : Scheme.{u}) (x : X)
    [IsDomain (X.presheaf.stalk x)] {C D : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  obtain ⟨R, g, hg, y, rfl⟩ := Scheme.exists_Spec_apply_eq x
  let e := (Spec.stalkIso R y).symm ≪≫ (asIso (g.stalkMap y)).symm
  have : IsDomain (Localization.AtPrime y.asIdeal) :=
    e.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have he : g ⁻¹' C = g ⁻¹' D :=
    LocalDomainComponents.Construction.affine_components_eq_of_domain_localization R y
      (preimage_mem_irreducibleComponents hC g.isOpenEmbedding ⟨g y, hxC, y, rfl⟩)
      (preimage_mem_irreducibleComponents hD g.isOpenEmbedding ⟨g y, hxD, y, rfl⟩)
      hxC hxD
  calc
    C = closure (g '' (g ⁻¹' C)) :=
      (closure_image_preimage_of_isPreirreducible g g.isOpenEmbedding.isOpenMap C
        ⟨y, hxC⟩ hC.1.2 (isClosed_of_mem_irreducibleComponents C hC)).symm
    _ = closure (g '' (g ⁻¹' D)) := by rw [he]
    _ = D := closure_image_preimage_of_isPreirreducible g g.isOpenEmbedding.isOpenMap D
      ⟨y, hxD⟩ hD.1.2 (isClosed_of_mem_irreducibleComponents D hD)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemeDomainComponents.Construction
