import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ContinuousPresentedPeriods

/-! # Holomorphic Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicMatrices

noncomputable section

/-! Holomorphic native period matrices in the same full integral frame
used to retain the actual family endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

theorem nativeFamilyFrame_holomorphic_matrices
    (F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
    (present : ∀ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    let : ∀ z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    ∃ U : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      U ⊆ F.neighborhood ∧ U ⊆ C.charts.charts.neighborhood ∧
      ∃ (d : ℕ) (e : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] (Fin d → ℂ))
        (T : ∀ z : U, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
        (marking : ∀ z : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin F.rank) (present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
        (matrix : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → (Fin F.rank → ℂ) →L[ℂ] (Fin d → ℂ)),
        (∀ (z : U) v, T z v =
          mfderiv (𝓘(ℝ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartModel C z))
            (𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety))
            (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).comparison.hom) 1
            (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) v)) ∧
        (∀ (z : U) i, (marking z i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety) =
          T z (F.periods z (Pi.single i 1))) ∧
        (∀ z : U, matrix z =
          (((T z).symm.trans e).toLinearEquiv.toLinearMap.comp
            (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z))).toContinuousLinearMap) ∧
        DifferentiableOn ℂ matrix U := by
  let : ∀ z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  let U := F.neighborhood ∩ C.charts.charts.neighborhood
  have hU : IsOpen U := F.isOpen.inter C.charts.charts.isOpen
  have hxN : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ C.charts.charts.neighborhood := by
    simpa only [RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter, AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id]
      using C.charts.charts.center
  have hxU : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ U := ⟨F.center, hxN⟩
  have hc (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ U) :
      (1 : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartPoints C z) ∈ (F.charts z).source ∧ F.charts z 1 = 0 ∧
        ContMDiffOn (𝓘(ℂ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartModel C z)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C)) 1
          (F.charts z) (F.charts z).source ∧
        ContMDiffOn (𝓘(ℂ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartModel C z)) 1
          (F.charts z).symm (F.charts z).target := by
    obtain ⟨h1, h0, _, _, _, _, _, hf, hi⟩ := F.chartData z hz.2
    exact ⟨h1, h0, hf.of_le (by simp), hi.of_le (by simp)⟩
  obtain ⟨d, e, T, marking, matrix, hT, hb, hm, hhol⟩ :=
    PELModuli.CMPoints.ContinuousPresentedPeriods.exists_holomorphic_presented_periods_on (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartFiber C)
      (fun z => present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)) F.charts U hc F.rank F.periods
      (fun z hz => F.full z hz.1) (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) hxU
      (F.continuous.mono Set.inter_subset_left)
      (fun i => (F.holomorphic i).mono Set.inter_subset_left)
  exact ⟨U, hU, hxU, Set.inter_subset_left, Set.inter_subset_right,
    d, e, T, marking, matrix, hT, hb, hm, hhol⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicMatrices
