import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Common Line Frames -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.CommonLineFrames.Construction

/-! Two actual line bundles have a common cover by frame neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem common_line_frame_neighborhood {X : Scheme.{u}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial x
  obtain ⟨V, hxV, ⟨d⟩⟩ := M.locallyTrivial x
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨L.frameRestrict inf_le_left e⟩, ⟨M.frameRestrict inf_le_right d⟩⟩

end OAI.AlgebraicGeometry.Picard.Homomorphisms.CommonLineFrames.Construction
