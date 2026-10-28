import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Trivial Bundle -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TrivialBundle.Construction.TrivialBundleFrame

noncomputable section

/-! A nonzero section of a trivial line bundle on a proper connected
reduced scheme over a field is a frame. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

universe u

variable {K : Type u} [Field K] (X : Over (Spec (.of K)))
variable [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]

theorem isIso {M : X.left.Modules} (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ M) (hs : s ≠ 0) : IsIso s := by
  let a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) := s ≫ e.hom
  have ha : a ≠ 0 := by
    intro h
    apply hs
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using h
  have hv : AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X.left a ≠ 0 := by
    intro h
    apply ha
    exact (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X.left).injective (h.trans (map_zero _).symm)
  have hu := (ProperFunctionsEq.Construction.ProperFunctions.section_eq_zero_or_isUnit X
    (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X.left a)).resolve_left hv
  have : IsIso (s ≫ e.hom) := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff a).mpr hu
  exact IsIso.of_isIso_comp_right s e.hom

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TrivialBundle.Construction.TrivialBundleFrame
