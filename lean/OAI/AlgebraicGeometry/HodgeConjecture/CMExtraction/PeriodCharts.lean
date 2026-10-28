import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodFamilies

/-! # Period Charts -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts

noncomputable section

/-! Construct period tests directly from a holomorphic map and an actual affine neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (Ω : Opens RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (c : Ω → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  (hc : ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) ∞ c)

def periodNeighborhood : Opens Ω :=
  ⟨c ⁻¹' (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U), (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U).isOpen.preimage hc.continuous⟩

def periodNeighborhoodMap : periodNeighborhood X U Ω c hc → Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U :=
  fun x => ⟨c x.val, x.property⟩

theorem periodNeighborhoodMap_smooth :
    ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) ∞
      (periodNeighborhoodMap X U Ω c hc) := by
  apply (ContMDiff.subtypeVal_comp_iff (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) _).mp
  exact hc.comp contMDiff_subtype_val

def affineCoordinateFamily (x : periodNeighborhood X U Ω c hc) (y : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) :=
  AffineEvaluation.Kaehler.affineOpenCharacter X U hU
    (periodNeighborhoodMap X U Ω c hc ((chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).symm y))

theorem affineCoordinateFamily_differentiable (x : periodNeighborhood X U Ω c hc)
    (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) :
    DifferentiableAt ℂ (fun y => affineCoordinateFamily X U hU Ω c hc x y a) x.val.val := by
  have hf := (HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U a).comp
    (periodNeighborhoodMap_smooth X U Ω c hc)
  have hs : ContMDiffAt 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) ∞
      (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).symm (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x x) :=
    contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (chart_mem_atlas RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x))
      ((chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).map_source (mem_chart_source RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x))
  have hd := (hf.contMDiffAt.comp (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x x) hs).contDiffAt.differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have heq : (fun y => affineCoordinateFamily X U hU Ω c hc x y a) =
      fun y => Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U a
        (periodNeighborhoodMap X U Ω c hc ((chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).symm y)) := by
    funext y
    exact AffineEvaluation.Kaehler.affineOpenCharacter_evaluation X U hU _ a
  rw [heq]
  exact hd

def localPeriodTest (x : periodNeighborhood X U Ω c hc) :
    AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x.val.val) ⟶ X :=
  PeriodFamilies.familyTest (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) x.val.val
    (affineCoordinateFamily X U hU Ω c hc x)
    (affineCoordinateFamily_differentiable X U hU Ω c hc x)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)

theorem localPeriodTest_germ (x : periodNeighborhood X U Ω c hc) :
    ∀ᶠ y in 𝓝 x.val.val, ∀ hy : y ∈ Ω,
      RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodTestPoint x.val.val y (localPeriodTest X U hU Ω c hc x) =
        c ⟨y, hy⟩ := by
  have hn : (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).target ∈ 𝓝 x.val.val :=
    (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).open_target.mem_nhds
      ((chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).map_source (mem_chart_source RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x))
  filter_upwards [hn] with y hy
  intro hyΩ
  have he : ((chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).symm y).val = (⟨y, hyΩ⟩ : Ω) := by
    apply Subtype.ext
    exact (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x).right_inv hy
  exact (PeriodFamilies.familyTest_point (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) x.val.val
    (affineCoordinateFamily X U hU Ω c hc x)
    (affineCoordinateFamily_differentiable X U hU Ω c hc x)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) y).trans
      ((AffineEvaluation.Kaehler.affineOpenCharacter_point X U hU _).trans (congrArg c he))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodCharts
