import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicMatrices
import OAI.RepresentationTheory.Theta.Geometric.FrameTangentComparison
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv

/-! # Marked Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedTransport

noncomputable section

/-! The holomorphic native period matrices use exactly the markings
identified by the constructed real transport of the same family frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff

local instance holomorphicMarkedTransport_varietyIntegral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance holomorphicMarkedTransport_varietySmooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem nativeFamilyFrame_holomorphic_marked_transport
    (present : ∀ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left)) :
    let P := fun z => present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    ∃ (U : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (_hU : IsOpen U) (hx : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ U)
      (_hF : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood)
      (d : ℕ) (e : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] (Fin d → ℂ))
      (T : ∀ z : U, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P z).variety)
      (marking : ∀ z : U, ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Fin F.rank) (P z).variety)
      (matrix : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → (Fin F.rank → ℂ) →L[ℂ] (Fin d → ℂ)),
      (∀ (z : U) i, (marking z i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P z).variety) = T z (F.periods z (Pi.single i 1))) ∧
      (∀ z : U, matrix z = (((T z).symm.trans e).toLinearEquiv.toLinearMap.comp
        (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap (marking z))).toContinuousLinearMap) ∧
      DifferentiableOn ℂ matrix U ∧
      ∀ (z : U) i,
        F.nativeRealTransport z (hN z.property) (P (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) (P z)
          (marking ⟨RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C, hx⟩ i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)).variety) =
            (marking z i : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (P z).variety) := by
  let : ∀ z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let P := fun z => present (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
  obtain ⟨U, hU, hx, hF, hN, d, e, T, marking, matrix, hT, hb, hm, hhol⟩ := HolomorphicMatrices.nativeFamilyFrame_holomorphic_matrices F present
  refine ⟨U, hU, hx, hF, hN, d, e, T, marking, matrix, hb, hm, hhol, ?_⟩
  intro z i
  let z₀ : U := ⟨RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C, hx⟩
  have h₀ (v : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C) :
      T z₀ v = F.presentedChartTangent (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) (RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartCenter_mem C) (P (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) v :=
    (hT z₀ v).trans (F.presentedChartTangent_derivative (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) (RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartCenter_mem C)
      (P (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) v).symm
  have hz (v : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartTangent C) : T z v = F.presentedChartTangent z (hN z.property) (P z) v :=
    (hT z v).trans (F.presentedChartTangent_derivative z (hN z.property) (P z) v).symm
  have ht : F.nativeRealTransport z (hN z.property) (P (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) (P z)
      (T z₀ (F.periods (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) (Pi.single i 1))) = T z (F.periods z (Pi.single i 1)) := by
    change F.presentedChartTangent z (hN z.property) (P z)
      (F.realTransport z ((F.presentedChartTangent (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) (RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartCenter_mem C)
        (P (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).symm (T z₀ (F.periods (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) (Pi.single i 1))))) = _
    rw [h₀, ContinuousLinearEquiv.symm_apply_apply]
    have hp : F.realTransport z (F.periods (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C) (Pi.single i 1)) =
        F.periods z (Pi.single i 1) :=
      congrArg (F.periods z) ((F.periods (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)).symm_apply_apply (Pi.single i 1))
    rw [hp, ← hz]
  exact (congrArg (F.nativeRealTransport z (hN z.property) (P (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) (P z)) (hb z₀ i)).trans
    (ht.trans (hb z i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedTransport
