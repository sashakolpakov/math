import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.Matrices
import OAI.RepresentationTheory.Theta.Geometric.FrameMarkingTransport

/-! # Marked Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The holomorphic native period matrices use exactly the markings
identified by the constructed real transport of the same family frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

local instance Holomorphic.MarkedTransport.holomorphicMarkedTransport_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance Holomorphic.MarkedTransport.holomorphicMarkedTransport_varietySmooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_holomorphic_marked_transport
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
    ∃ (U : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (_hU : IsOpen U) (hx : Intrinsic.FamilyFrames.familyChartCenter C ∈ U)
      (_hF : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood)
      (d : ℕ) (e : Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] (Fin d → ℂ))
      (T : ∀ z : U, Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P z).variety)
      (marking : ∀ z : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin F.rank) (P z).variety)
      (matrix : Intrinsic.FamilyFrames.FamilyChartBase C → (Fin F.rank → ℂ) →L[ℂ] (Fin d → ℂ)),
      (∀ (z : U) i, (marking z i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P z).variety) = T z (F.periods z (Pi.single i 1))) ∧
      (∀ z : U, matrix z = (((T z).symm.trans e).toLinearEquiv.toLinearMap.comp
        (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z))).toContinuousLinearMap) ∧
      DifferentiableOn ℂ matrix U ∧
      ∀ (z : U) i,
        F.nativeRealTransport z (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z)
          (marking ⟨Intrinsic.FamilyFrames.familyChartCenter C, hx⟩ i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety) =
            (marking z i : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P z).variety) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
  obtain ⟨U, hU, hx, hF, hN, d, e, T, marking, matrix, hT, hb, hm, hhol⟩ := F.holomorphic_matrices present
  refine ⟨U, hU, hx, hF, hN, d, e, T, marking, matrix, hb, hm, hhol, ?_⟩
  intro z i
  let z₀ : U := ⟨Intrinsic.FamilyFrames.familyChartCenter C, hx⟩
  have h₀ (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
      T z₀ v = F.presentedChartTangent (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C) (P (Intrinsic.FamilyFrames.familyChartCenter C)) v :=
    (hT z₀ v).trans (F.presentedChartTangent_derivative (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C)
      (P (Intrinsic.FamilyFrames.familyChartCenter C)) v).symm
  have hz (v : Intrinsic.FamilyFrames.FamilyChartTangent C) : T z v = F.presentedChartTangent z (hN z.property) (P z) v :=
    (hT z v).trans (F.presentedChartTangent_derivative z (hN z.property) (P z) v).symm
  have ht := F.nativeRealTransport_marked_vector z (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z)
    (T z₀) (T z) h₀ hz (Pi.single i 1)
  exact (congrArg (F.nativeRealTransport z (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z)) (hb z₀ i)).trans
    (ht.trans (hb z i).symm)

end

end OAI.RepresentationTheory.Theta.Geometric
