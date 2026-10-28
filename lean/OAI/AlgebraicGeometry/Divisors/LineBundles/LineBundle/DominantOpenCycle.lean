import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantOpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SectionCycleTransport

/-! # Dominant Open Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantOpenCycle.Cycles

noncomputable section

/-! # LineBundleCycles: the complete actual divisor of a dominant rational-section pullback commutes with open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y W Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [AlgebraicGeometry.IsNoetherian W] [AlgebraicGeometry.IsNoetherian Z]
    (f : X ⟶ Y) (k : W ⟶ X) [IsOpenImmersion k] (j : Z ⟶ Y) [IsOpenImmersion j]
    (q : W ⟶ Z) (hcomm : k ≫ f = q ≫ j)
    (hf : f (genericPoint X) = genericPoint Y) (hq : q (genericPoint W) = genericPoint Z)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

omit [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z] in
include hcomm in
theorem dominantPullback_section_openSquare (a : Y.functionFieldˣ) :
    ((L.pullback j).pullback q).rationalSectionPointCycleWithCoefficient
        ((L.pullback j).dominantPullbackSectionCoefficient q hq (L.openPullbackSectionCoefficient j a)) =
      Finsupp.comapDomain k ((L.pullback f).rationalSectionPointCycleWithCoefficient
        (L.dominantPullbackSectionCoefficient f hf a)) k.isOpenEmbedding.injective.injOn := by
  let A := (L.pullback f).pullback k
  let B := (L.pullback j).pullback q
  let e : A.sheaf ≅ B.sheaf := Module.PullbackSquareSections.BundleCycles.modulePullbackSquareIso f k j q hcomm L.sheaf
  let b := (L.pullback f).openPullbackSectionCoefficient k (L.dominantPullbackSectionCoefficient f hf a)
  have hc := DominantOpenSquare.Cycles.dominantPullbackSectionCoefficient_openSquare f k j q hcomm hf hq L a
  have hi := SectionCycleTransport.Cycles.lineBundleIso_section_pointCycle (L := A) (M := B) e b
  have ho := (L.pullback f).openPullback_section_pointCycle k (L.dominantPullbackSectionCoefficient f hf a)
  exact (congrArg B.rationalSectionPointCycleWithCoefficient hc.symm).trans (hi.trans ho)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantOpenCycle.Cycles
