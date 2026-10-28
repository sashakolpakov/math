import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupEvaluation

/-! # Compact Left Cup Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCupTrace.Constructions

noncomputable section

/-! Left cup by a degree-two class has exactly the native compact-support evaluation as its trace. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem compactCohomologyLeftTwoCup_trace (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    (q : ℕ) (h : 2+q=2*d)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) 2)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) h)
        (CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of M) 2 q a b)) =
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d 2 q h a b := by
  have hc := CompactLeftCup.Constructions.compactCohomologyLeftCup_graded_comm (TopCat.of M) 2 q a b
  simp only [pow_mul, neg_one_sq, one_pow, one_smul] at hc
  rw [hc, CompactCupEvaluation.Constructions.compactCohomologyDegreeCast_trans (TopCat.of M) (Nat.add_comm q 2) h (by omega)]
  exact CompactCupTrace.Constructions.compactCohomologyRightCup_trace d q 2 (by omega) a b

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCupTrace.Constructions
