import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentGlobalFrameGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DualFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts

/-! # Test Line Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TestLineTriviality

noncomputable section

/-! Every actual line bundle on the dual-number test is trivial.
Its underlying scheme has one point, so an original local frame covers
the entire scheme. No assertion of reducedness is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem lineBundle_trivial_of_single_point (X : Scheme.{0}) [Subsingleton X] [Nonempty X]
    (L : HilbertConstruction.Line.Bundles.LineBundle X) : Nonempty (L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X) := by
  let x : X := Classical.arbitrary X
  obtain ⟨s, hs⟩ := LineFrameAtlas.localLineFrames_cover L x
  have hc : iSup (fun _ : Unit => s.domain) = ⊤ := by
    apply top_unique
    intro y _
    apply Opens.mem_iSup.mpr
    exact ⟨(), (Subsingleton.elim x y) ▸ hs⟩
  obtain ⟨e, _⟩ := CoherentGlobalFrameGluing.exists_global_frame_agreeing (fun _ : Unit => s) hc
    (fun _ _ => s.transition_self _ inf_le_left)
  exact ⟨e⟩

theorem dualNumberTest_single_point : Subsingleton (LieRanks.dualNumberTest ℂ).left :=
  NumberSpectrum.dualNumber_primeSpectrum_subsingleton

theorem dualNumberTestLine_trivial (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ).left) :
    Nonempty (L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule (LieRanks.dualNumberTest ℂ).left) := by
  let : Subsingleton (LieRanks.dualNumberTest ℂ).left := dualNumberTest_single_point
  let : Nonempty (LieRanks.dualNumberTest ℂ).left := inferInstanceAs (Nonempty (Spec (.of (DualNumber ℂ))))
  exact lineBundle_trivial_of_single_point (LieRanks.dualNumberTest ℂ).left L

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TestLineTriviality
