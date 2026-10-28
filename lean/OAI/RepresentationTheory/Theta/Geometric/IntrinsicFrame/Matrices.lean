import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames
import OAI.RepresentationTheory.Theta.Geometric.Period.PointsHolomorphicPresentedPeriods

/-! # Matrices -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.Matrices

noncomputable section

/-! Holomorphic native period matrices in the same full integral frame
used to retain the actual family endomorphisms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.holomorphic_matrices
    (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      U ⊆ F.neighborhood ∧ U ⊆ C.charts.charts.neighborhood ∧
      ∃ (d : ℕ) (e : Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] (Fin d → ℂ))
        (T : ∀ z : U, Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (present (Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
        (marking : ∀ z : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin F.rank) (present (Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
        (matrix : Intrinsic.FamilyFrames.FamilyChartBase C → (Fin F.rank → ℂ) →L[ℂ] (Fin d → ℂ)),
        (∀ (z : U) v, T z v =
          mfderiv (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z))
            (𝓘(ℝ, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (present (Intrinsic.FamilyFrames.familyChartParameter C z)).variety))
            (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (present (Intrinsic.FamilyFrames.familyChartParameter C z)).comparison.hom) 1
            (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) v)) ∧
        (∀ (z : U) i, (marking z i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (present (Intrinsic.FamilyFrames.familyChartParameter C z)).variety) =
          T z (F.periods z (Pi.single i 1))) ∧
        (∀ z : U, matrix z =
          (((T z).symm.trans e).toLinearEquiv.toLinearMap.comp
            (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z))).toContinuousLinearMap) ∧
        DifferentiableOn ℂ matrix U := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  let U := F.neighborhood ∩ C.charts.charts.neighborhood
  have hU : IsOpen U := F.isOpen.inter C.charts.charts.isOpen
  have hxN : Intrinsic.FamilyFrames.familyChartCenter C ∈ C.charts.charts.neighborhood := by
    simpa only [Intrinsic.FamilyFrames.familyChartCenter, AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id]
      using C.charts.charts.center
  have hxU : Intrinsic.FamilyFrames.familyChartCenter C ∈ U := ⟨F.center, hxN⟩
  have hc (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ U) :
      (1 : Intrinsic.FamilyFrames.FamilyChartPoints C z) ∈ (F.charts z).source ∧ F.charts z 1 = 0 ∧
        ContMDiffOn (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartModel C z)) (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartTangent C)) 1
          (F.charts z) (F.charts z).source ∧
        ContMDiffOn (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartTangent C)) (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartModel C z)) 1
          (F.charts z).symm (F.charts z).target := by
    obtain ⟨h1, h0, _, _, _, _, _, hf, hi⟩ := F.chartData z hz.2
    exact ⟨h1, h0, hf.of_le (by simp), hi.of_le (by simp)⟩
  obtain ⟨d, e, T, marking, matrix, hT, hb, hm, hhol⟩ :=
    AlgebraicGeometry.PELModuli.CMPoints.ContinuousPresentedPeriods.exists_holomorphic_presented_periods_on (Intrinsic.FamilyFrames.familyChartFiber C)
      (fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)) F.charts U hc F.rank F.periods
      (fun z hz => F.full z hz.1) (Intrinsic.FamilyFrames.familyChartCenter C) hxU
      (F.continuous.mono Set.inter_subset_left)
      (fun i => (F.holomorphic i).mono Set.inter_subset_left)
  exact ⟨U, hU, hxU, Set.inter_subset_left, Set.inter_subset_right,
    d, e, T, marking, matrix, hT, hb, hm, hhol⟩

end

end OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.Matrices
