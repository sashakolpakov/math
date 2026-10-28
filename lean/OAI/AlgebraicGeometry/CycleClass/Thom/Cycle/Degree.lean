import OAI.AlgebraicGeometry.CycleClass.Geometric.Span
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Degree.Constructions.Class

noncomputable section

/-! Explicit degree transports for the native cycle class and for the
ordinary cup of projection pullbacks. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Products.CupCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem rationalCycleClass_as_cast {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (A : Geometric.DimensionCycles.DimensionCycleSupport V p) : A.rationalCycleClass =
      cast (congrArg (fun n => (V.rationalCohomology n : Type)) (two_mul p))
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
          (Set.range A.analyticInclusion)ᶜ (2 * p) A.rationalSupportedCycleClass) := by
  unfold Geometric.DimensionCycles.DimensionCycleSupport.rationalCycleClass
  rfl

theorem projectionCup_degreeTransport {X Y Z : TopCat.{0}} (f : Z ⟶ X) (g : Z ⟶ Y)
    {m m' n n' k k' : ℕ} (hm : m = m') (hn : n = n')
    (ht : m + n = k) (ht' : m' + n' = k') (hk : k = k')
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X m)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y n) :
    cast (congrArg (fun j => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Z j : Type)) hk)
      (cast (congrArg (fun j => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Z j : Type)) ht)
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) Z m n
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f m a)
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g n b))) =
    cast (congrArg (fun j => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Z j : Type)) ht')
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) Z m' n'
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f m'
          (cast (congrArg (fun j => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X j : Type)) hm) a))
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g n'
          (cast (congrArg (fun j => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y j : Type)) hn) b))) := by
  subst m'
  subst n'
  subst ht
  subst ht'
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Degree.Constructions.Class
