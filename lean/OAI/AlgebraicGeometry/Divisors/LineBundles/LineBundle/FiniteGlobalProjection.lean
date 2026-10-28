import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantGlobalFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.DivisorNorm

/-! # Finite Global Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteGlobalProjection.Cycles

noncomputable section

/-! # LineBundleCycles: exact finite projection of actual rational-section divisors in a global frame -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y} (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule Y)

include gY e in
theorem finitePushforward_lineBundleSection_globalFrame (a : Y.functionFieldˣ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f
        ((L.pullback f).rationalSectionPointCycleWithCoefficient (L.dominantPullbackSectionCoefficient f hη a)) =
      (f.residueDegree (genericPoint X) : ℚ) • L.rationalSectionPointCycleWithCoefficient a := by
  rw [GlobalDivisor.Cycles.lineBundleGlobal_section_pointCycle (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f),
    DominantGlobalFrame.Cycles.dominantPullbackSectionCoefficient_globalFrame f hη e a,
    GlobalDivisor.Cycles.lineBundleGlobal_section_pointCycle e a]
  exact Finite.DivisorNorm.BundleCycles.finitePushforward_pulledPrincipalDivisor f hη gY (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteGlobalProjection.Cycles
