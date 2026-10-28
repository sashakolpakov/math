/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.SmoothPairCoclassSection

/-! # Smooth Pair Germ -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The global exactly normalized smooth-support coclass section

-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular
open _root_.TopCat.Presheaf

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

@[simp] theorem ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection_germ (x : ComplexPoint.Basic.ComplexSchemePoint X) :
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection X Y i m d) =
        ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d x :=
  AlgebraicTopology.Sheaf.MapOfLocalStalks.TopCat.sectionOfLocallyRepresentable_germ
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d) x

end

end OAI.AlgebraicGeometry
