import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveLogarithmicCover
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

/-! # Projective Chern Cocycle -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveChernCocycle.CM.Construction

noncomputable section

/-! The homogeneous-coordinate logarithms give an actual rational
singular degree-two class via their integral Čech defects. -/

open _root_.TopologicalSpace Set
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [NormalSpace M]
  {ι : Type} [Fintype ι]
  (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

abbrev projectiveChernCover := (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).cover

def projectiveLogCech : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain
    (TopCat.of M) (projectiveChernCover p hp hhol) :=
  fun a => ((ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).logarithm (a 0) (a 1)).comp
    (DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap
      (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1)))

theorem projectiveLogCech_exp (a : Fin 2 → M × ι)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (projectiveChernCover p hp hhol) a) :
    Complex.exp (projectiveLogCech p hp hhol a x) = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (a 0).2 (a 1).2 (p x.val) :=
  (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).exp_logarithm (a 0) (a 1)
    ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 x.property, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 x.property⟩

theorem projectiveLogCech_cocycle : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle
    (TopCat.of M) (projectiveChernCover p hp hhol) (projectiveLogCech p hp hhol) := by
  intro a x
  let U := projectiveChernCover p hp hhol
  have hlog (j : Fin 3) : Complex.exp
      (DivisorClass.Chern.LogCech.RationalCech.edgeLog (TopCat.of M) U (projectiveLogCech p hp hhol) j a x) =
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (a (j.succAbove 0)).2 (a (j.succAbove 1)).2 (p x.val) := by
    exact projectiveLogCech_exp p hp hhol (a ∘ j.succAbove) _
  rw [hlog 2, hlog 0, hlog 1]
  change Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (a 0).2 (a 1).2 (p x.val) * Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (a 1).2 (a 2).2 (p x.val) =
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio (a 0).2 (a 2).2 (p x.val)
  have hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (a 0).2 (p x.val) :=
    (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property)
  have hj : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch (a 1).2 (p x.val) :=
    (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)
  rw [Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula (a 0).2 (a 1).2 (a 2).2 (p x.val) hi]
  exact mul_div_cancel₀ _ ((Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero (a 0).2 (a 1).2 (p x.val) hi).mp hj)

def projectiveLogarithmicClassQ :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) 2 :=
  DivisorClass.Chern.LogCech.RationalCech.logarithmicSingularClass (TopCat.of M)
    (projectiveChernCover p hp hhol) (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).covers
    (projectiveLogCech p hp hhol) (projectiveLogCech_cocycle p hp hhol)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveChernCocycle.CM.Construction
