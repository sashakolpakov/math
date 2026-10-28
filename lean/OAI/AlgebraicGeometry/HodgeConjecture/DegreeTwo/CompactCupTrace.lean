import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCohomologyCup
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

/-! # Compact Cup Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupTrace.Constructions

noncomputable section

/-! The actual compact cup integral is precisely native cap evaluation. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction.Cycles
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem complexManifoldTrace_degreeCast_stage (p : ℕ) (hp : p=2*d) (K : Compacts M)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ p) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) hp)
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K p a)) =
      AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) (K : Set M)ᶜ p a
        (AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexCompactClassInDegree d p hp K) := by
  subst p
  exact AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_stage_apply d K a

theorem compactCohomologyRightCup_trace (p q : ℕ) (hpq : p+q=2*d)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q)
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) hpq)
        (CompactCohomologyCup.Constructions.compactCohomologyRightCup (TopCat.of M) p q a b)) =
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d q p (by omega) a b := by
  obtain ⟨K,b,rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ) (TopCat.of M) p b
  have hs := congrArg
    (fun z => AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) hpq) z))
    (CompactCohomologyCup.Constructions.compactCohomologyRightCup_stage (TopCat.of M) p q a K b)
  have ht := complexManifoldTrace_degreeCast_stage d (p+q) hpq K
    (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of M) (K : Set M)ᶜ p q b a)
  have he := CycleClass.Geometric.RelativeCupCapAdjunction.Cycles.relativeAbsoluteCohomologyCup_evaluation_cap (TopCat.of M) (K : Set M)ᶜ p q b a
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexCompactClassInDegree d (p+q) hpq K)
  exact hs.trans (ht.trans (he.trans
    (AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation_stage d q p (by omega) a K b).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupTrace.Constructions
