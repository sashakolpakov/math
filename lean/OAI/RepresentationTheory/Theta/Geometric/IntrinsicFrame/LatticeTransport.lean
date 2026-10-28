import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.Exponential
import OAI.RepresentationTheory.Theta.Geometric.MovingLatticeAction

/-! # Lattice Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The real period-frame comparison identifies every nearby full
native lattice with the central lattice, without changing its marking. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.Topology

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.LatticeTransport.nativeFrameLatticeTransport_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C) [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.realTransport (z : Intrinsic.FamilyFrames.FamilyChartBase C) : Intrinsic.FamilyFrames.FamilyChartTangent C ≃L[ℝ] Intrinsic.FamilyFrames.FamilyChartTangent C :=
  (F.periods (Intrinsic.FamilyFrames.familyChartCenter C)).symm.trans (F.periods z)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralLattice : Submodule ℤ (Intrinsic.FamilyFrames.FamilyChartTangent C) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  exact ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C))
    (F.charts (Intrinsic.FamilyFrames.familyChartCenter C))

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.realTransport_central (v : Intrinsic.FamilyFrames.FamilyChartTangent C) :
    F.realTransport (Intrinsic.FamilyFrames.familyChartCenter C) v = v :=
  (F.periods (Intrinsic.FamilyFrames.familyChartCenter C)).apply_symm_apply v

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.realTransport_lattice (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood) :
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
    let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
    ∀ v : Intrinsic.FamilyFrames.FamilyChartTangent C,
      F.realTransport z v ∈ ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z) ↔
        v ∈ F.centralLattice := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  let Λ := fun w : F.neighborhood => ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := Intrinsic.FamilyFrames.FamilyChartModel C w) (F.charts w)
  choose b hb using fun w : F.neighborhood => F.full w w.property
  exact MovingLatticeAction.movingLattice_transport_iff Λ b (fun w : F.neighborhood => F.periods w) hb
    ⟨Intrinsic.FamilyFrames.familyChartCenter C, F.center⟩ ⟨z, hz⟩

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.realTransport_continuous :
    ContinuousOn (fun z => (F.realTransport z).toContinuousLinearMap) F.neighborhood := by
  have h := F.continuous.clm_comp (continuousOn_const
    (c := (F.periods (Intrinsic.FamilyFrames.familyChartCenter C)).symm.toContinuousLinearMap))
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric
