import OAI.RepresentationTheory.Theta.Geometric.CentralTorusEndomorphism
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusMap
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrameActions

/-! # Endomorphism Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The same actual fixed-torus transport commutes locally with every
original family endomorphism, as proved from its integral frame matrix. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.EndomorphismTransport.nativeFrameEndomorphismTransport_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_endomorphism_torus_transport
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (k : G.scheme ⟶ G.scheme) [IsMonHom k] :
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ hU : U ⊆ F.neighborhood, ∀ (z : U) (t : F.CentralTorus),
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C z))
          (F.torusFiberMap z (hU z.property) t) =
            F.torusFiberMap z (hU z.property) (F.centralTorusEndomorphism P k t) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  obtain ⟨U, D, hUopen, hxU, hU, _, hD, hmatrix⟩ := F.endomorphism_matrices_locally_constant k
  refine ⟨U, hUopen, hxU, hU, ?_⟩
  intro z t
  let K := ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C z)
  let : IsMonHom K := ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G k _
  induction t using Quotient.inductionOn with
  | h v =>
    rw [F.centralTorusEndomorphism_mk P k (D (Intrinsic.FamilyFrames.familyChartCenter C)) (hD _ hxU)]
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K (F.transportedExponential z v).toMul =
      (F.transportedExponential z (D (Intrinsic.FamilyFrames.familyChartCenter C) v)).toMul
    rw [F.transportedExponential_apply, F.transportedExponential_apply]
    have he := ChartEndomorphismExponential.nativeChartDerivative_exp (Intrinsic.FamilyFrames.familyChartFiber C z) (F.charts z) K (D z)
      (hD z z.property) (F.realTransport z v)
    have hm := ChartEndomorphismExponential.conjugatedMatrices_intertwine (F.periods (Intrinsic.FamilyFrames.familyChartCenter C)) (F.periods z)
      (D (Intrinsic.FamilyFrames.familyChartCenter C)) (D z) (hmatrix z z.property) v
    exact he.trans (congrArg (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (G := Intrinsic.FamilyFrames.FamilyChartPoints C z)
      (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z)) hm)

end

end OAI.RepresentationTheory.Theta.Geometric
