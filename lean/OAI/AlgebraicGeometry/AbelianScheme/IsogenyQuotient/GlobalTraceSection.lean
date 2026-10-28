import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalTraceSections

/-! # Global Trace Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalTraceSection.Construction

noncomputable section

/-! The finite-flat trace is an actual global section of the original
line bundle. Neither a constant degree nor reducedness is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (q : X ⟶ Y)
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf)

theorem existsUnique_globalTraceSection :
    ∃! a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf,
      ∀ U : LocalTraceSections.Construction.TraceFrameOpen q L, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.2.openSet.ι a = LocalTraceSections.Construction.localTraceSection q L U z := by
  exact OpenSectionGluing.Construction.existsUnique_section_of_basis_refinements
    (fun U : LocalTraceSections.Construction.TraceFrameOpen q L => U.2.openSet) (LocalTraceSections.Construction.traceFrameOpens_isBasis q L)
    (fun U => LocalTraceSections.Construction.localTraceSection q L U z) (fun V U h => LocalTraceSections.Construction.localTraceSection_refine q L V U h z)

def finiteFlatTraceSection : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf :=
  (existsUnique_globalTraceSection q L z).choose

theorem finiteFlatTraceSection_restrict (U : LocalTraceSections.Construction.TraceFrameOpen q L) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.2.openSet.ι (finiteFlatTraceSection q L z) = LocalTraceSections.Construction.localTraceSection q L U z :=
  (existsUnique_globalTraceSection q L z).choose_spec.1 U

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalTraceSection.Construction
