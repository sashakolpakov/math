import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TraceBaseChangeCharts

/-! # Global Trace Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalTraceBaseChange.Construction

noncomputable section

/-! The actual global trace of a line-bundle section commutes with
every scheme base change, without restrictions on the parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false in
theorem finiteFlatTraceSection_baseChange
    {X Y X' Y' : Scheme.{u}} (q : X ⟶ Y) (q' : X' ⟶ Y')
    (j : X' ⟶ X) (i : Y' ⟶ Y) (hs : IsPullback j q' q i)
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
    [IsFinite q'] [Flat q'] [LocallyOfFinitePresentation q']
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i (GlobalTraceSection.Construction.finiteFlatTraceSection q L z) =
      GlobalTraceSection.Construction.finiteFlatTraceSection q' (L.pullback i) (SquareSectionComposition.Construction.pullbackSquareSection q q' j i hs.w z) := by
  let B := {p : LocalTraceSections.Construction.TraceFrameOpen q L × LocalTraceSections.Construction.TraceFrameOpen q' (L.pullback i) //
    p.2.2.openSet ≤ i ⁻¹ᵁ p.1.2.openSet}
  let opens (b : B) := b.val.2.2.openSet
  have hcover : ∀ y : Y', ∃ b : B, y ∈ opens b := by
    intro y
    obtain ⟨U, hyU⟩ := LocalTraceSections.Construction.traceFrameOpens_cover q L (i y)
    obtain ⟨V, hyV⟩ := LocalTraceSections.Construction.traceFrameOpens_cover q' (L.pullback i) y
    obtain ⟨_, ⟨W : Y'.Opens, hW, rfl⟩, hyW, hWV⟩ :=
      Y'.isBasis_affineOpens.exists_subset_of_mem_open
        (show y ∈ V.2.openSet ⊓ i ⁻¹ᵁ U.2.openSet from ⟨hyV, hyU⟩)
        (V.2.openSet ⊓ i ⁻¹ᵁ U.2.openSet).isOpen
    exact ⟨⟨(U, ⟨V.1, V.2.restrictAffine W hW (hWV.trans inf_le_left)⟩),
      hWV.trans inf_le_right⟩, hyW⟩
  apply AbelianModuli.HilbertConstruction.Module.MapCoverEquality.moduleMap_eq_of_pullback_cover opens hcover
  intro b
  apply (cancel_epi (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (opens b).ι).inv).mp
  exact TraceBaseChangeCharts.Construction.finiteFlatTraceSection_baseChange_on_chart q q' j i hs L z
    b.val.1 b.val.2 b.property

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalTraceBaseChange.Construction
