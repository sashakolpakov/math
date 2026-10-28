/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.ComponentSupportExtension

/-! # Component Support Iso Hom -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Unique extension across a cycle component's singular boundary

-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

@[simp]
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso_hom :
    (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportExtensionIso X x hx).hom =
      HomologicalComplex.homologyMap (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)) := rfl

end

end OAI.AlgebraicGeometry
