import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Singular
import OAI.AlgebraicGeometry.DivisorClass.Chern.ContinuousHolomorphicLog
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogIntegralSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogObstruction

/-! # Chern Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChernSheaf

noncomputable section

/-! The constructed holomorphic bundle's original Chern class has an actual integral sheaf lift. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [CompactSpace M] [NormalSpace M]

theorem holomorphicLogCech_holomorphic (u : Connecting.holomorphicUnitCohomology E M)
    (a : Fin 2 → Singular.HolomorphicLogIndex E M u) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (Singular.holomorphicLogCech E M u a) := by
  let U := Singular.holomorphicLogCover E M u
  have ha : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤
      CohomologyTransitions.holomorphicCohomologyDomain E M u (a 0).2.val ⊓
        CohomologyTransitions.holomorphicCohomologyDomain E M u (a 1).2.val := by
    exact le_inf ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0).trans (Singular.holomorphicLogCover_subset E M u (a 0)))
      ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1).trans (Singular.holomorphicLogCover_subset E M u (a 1)))
  let g : Exponential.HolomorphicFunction (E := E) (M := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :=
    ⟨fun x => (CohomologyTransitions.holomorphicCohomologyTransition E M u (a 0).2.val (a 1).2.val).val
        (Opens.inclusion ha x),
      (CohomologyTransitions.holomorphicCohomologyTransition E M u (a 0).2.val (a 1).2.val).val.property.comp
        (contMDiff_inclusion ha)⟩
  exact ContinuousHolomorphicLog.continuous_logarithm_holomorphic g (Singular.holomorphicLogCech E M u a)
    (Singular.exp_holomorphicLogCech E M u a)

def holomorphicIntegralChernClass (u : Connecting.holomorphicUnitCohomology E M) :
    CategoryTheory.Sheaf.H (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)) 2 :=
  LogIntegralSheaf.logarithmicIntegralSheafClass (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCech E M u)
    (Singular.holomorphicLogCech_cocycle E M u)
    (Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCover_covers E M u))

variable [MetrizableSpace M] [StronglyLocallyContractibleSpace M] [LocallyPathConnectedSpace M]

theorem holomorphicIntegralChernClass_rationalize (u : Connecting.holomorphicUnitCohomology E M) :
    Rational.HolomorphicPeriod.integralToRationalSheafCohomology M (holomorphicIntegralChernClass E M u) =
      Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1 (Singular.holomorphicFirstChernClassQ E M u) :=
  LogIntegralSheaf.logarithmicIntegralSheafClass_rationalize (X := TopCat.of M)
    (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCech E M u)
    (Singular.holomorphicLogCech_cocycle E M u) (Singular.holomorphicLogCover_covers E M u)

theorem holomorphicFirstChernClassQ_obstruction (u : Connecting.holomorphicUnitCohomology E M) :
    Rational.HolomorphicPeriod.rationalHolomorphicObstruction E M
      (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1 (Singular.holomorphicFirstChernClassQ E M u)) = 0 :=
  LogObstruction.holomorphicLogCech_betti_obstruction E M (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCech E M u)
    (Singular.holomorphicLogCech_cocycle E M u) (holomorphicLogCech_holomorphic E M u)
    (Singular.holomorphicLogCover_covers E M u)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChernSheaf
