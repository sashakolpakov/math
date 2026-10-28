import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BerryLogarithmicDescent
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ContinuousLogarithmSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen

/-! # Projective Logarithmic Cover -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveLogarithmicCover.CM.Construction

noncomputable section

/-! A single refinement of the actual projective cover carries
holomorphic logarithms of all homogeneous-coordinate transitions. -/

open _root_.TopologicalSpace Set
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem logarithmicRefinement_holomorphic (U : ι → Opens M)
    (g : ∀ i j, C((U i ⊓ U j : Opens M), ℂ))
    (hg : ∀ i j, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (g i j))
    (r : DivisorClass.Chern.LogRefinementOpen.Construction.LogarithmicRefinement U g) (a b : M × ι) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (r.logarithm a b) := by
  let hsub : r.cover a ⊓ r.cover b ≤ U a.2 ⊓ U b.2 := inf_le_inf (r.subset a) (r.subset b)
  have hmap := (hg a.2 b.2).comp (contMDiff_inclusion (I := 𝓘(ℂ, E)) (n := ∞) hsub)
  exact ContinuousLogarithmSmooth.CM.Construction.continuous_logarithm_contMDiff (fun x => g a.2 b.2 (Opens.inclusion hsub x))
    (r.logarithm a b) hmap (r.logarithm a b).continuous (r.exp_logarithm a b)

variable (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

include hhol in
theorem projectiveTransition_holomorphic (i j : ι) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞
      (fun x : (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i ⊓ ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp j : Opens M) =>
        Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i x.val j) := by
  exact (contMDiffOn_pi_space.mp (hhol i) j).comp_contMDiff
    (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ∞)) (fun x => x.property.1)

def projectiveTransition (i j : ι) :
    C((ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i ⊓ ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp j : Opens M), ℂ) :=
  ⟨fun x => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i x.val j,
    (projectiveTransition_holomorphic p hp hhol i j).continuous⟩

theorem projectiveTransition_ne_zero (i j : ι)
    (x : (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i ⊓ ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp j : Opens M)) :
    projectiveTransition p hp hhol i j x ≠ 0 :=
  (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j (p x.val) x.property.1).mp x.property.2

variable [NormalSpace M]

def projectiveLogRefinement : DivisorClass.Chern.LogRefinementOpen.Construction.LogarithmicRefinement
    (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp) (projectiveTransition p hp hhol) :=
  Classical.choice (DivisorClass.Chern.LogRefinementOpen.Construction.nonempty_logarithmicRefinement
    (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp) (ProjectiveGluing.CM.Construction.projectiveLift_cover p hp)
    (projectiveTransition p hp hhol) (projectiveTransition_ne_zero p hp hhol))

theorem projectiveLogRefinement_holomorphic (a b : M × ι) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ ((projectiveLogRefinement p hp hhol).logarithm a b) :=
  logarithmicRefinement_holomorphic (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp) (projectiveTransition p hp hhol)
    (projectiveTransition_holomorphic p hp hhol) (projectiveLogRefinement p hp hhol) a b

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveLogarithmicCover.CM.Construction
