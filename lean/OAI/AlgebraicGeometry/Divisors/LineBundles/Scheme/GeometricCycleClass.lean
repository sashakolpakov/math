import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ProjectiveCycleClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteCycleClass
import OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace

/-! # Geometric Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GeometricCycleClass.BundleCycles

noncomputable section

/-! The general smooth-scheme cycle class agrees on projective varieties
with the independently defined geometric fundamental-trace class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) := inferInstanceAs (MetrizableSpace V.analyticSpace)

theorem schemeCycleClass_projective :
    AbsoluteCycleClass.BundleCycles.schemeCycleClass V.toOver Z.val p Z.dimension_add_codimension = Z.rationalCycleClass :=
  congrArg (fun a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range Z.analyticInclusion)ᶜ (2 * p) =>
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (two_mul p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ (2 * p) a)) (ProjectiveCycleClass.BundleCycles.schemeSupportedCycleClass_projective V p Z)

theorem schemeCycleClass_geometric :
    AbsoluteCycleClass.BundleCycles.schemeCycleClass V.toOver Z.val p Z.dimension_add_codimension = Z.geometricCycleClass :=
  (schemeCycleClass_projective V p Z).trans (CycleClass.Thom.GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric Z)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GeometricCycleClass.BundleCycles
