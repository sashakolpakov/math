import OAI.AlgebraicGeometry.ComplexPoint.BasicNe
import OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import OAI.AlgebraicGeometry.ComplexPoint.Manifold
import OAI.AlgebraicGeometry.Smooth.Equidimensional
import OAI.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

/-! # Projective Paracompact -/

namespace OAI.AlgebraicGeometry.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Paracompact open subsets of smooth projective analytifications

A smooth projective complex variety has a compact Hausdorff analytification and algebraic
coordinate charts modeled on a finite-dimensional complex vector space. Every open subset is
therefore paracompact. This supplies the hereditary-paracompactness input for the flasque
singular-cochain resolution.
-/

open _root_.TopologicalSpace
open _root_.CategoryTheory

variable (X : Over (Spec ↧ℂ))
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Every open subset of a smooth projective complex analytification is paracompact. -/
theorem Basic.ComplexSchemePoint.openParacompactSpace [IsIntegral X.left] [Smooth X.hom]
    (U : Opens (Basic.ComplexSchemePoint X)) : ParacompactSpace U :=
  Topology.Foundations.ChartedSpaceParacompact.TopologicalSpace.opens_paracompactSpace_of_compact_chartedSpace (H := Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) U

end

end OAI.AlgebraicGeometry.ComplexPoint
