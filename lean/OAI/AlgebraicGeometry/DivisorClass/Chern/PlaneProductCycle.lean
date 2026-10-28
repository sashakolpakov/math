import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductTo
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.FillingCycle

/-! # Plane Product Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCycle

noncomputable section

/-! The actual disk cross filling is a relative cycle with the displayed
punctured product boundary. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (m q : ℕ)
variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
variable (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
  (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
variable (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
  (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z)

def fullPlaneProductBoundaryCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))))) (q + 3) :=
  ⟨PlaneProductTo.fullPlaneProductBoundaryChain m q B z, by
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    let X := TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))
    let j := CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X ({0}ᶜ)
    have hj : Mono (j.f (q + 2)) :=
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_degreewiseShortExact ℚ X ({0}ᶜ) (q + 2)).mono_f
    apply (ModuleCat.mono_iff_injective _).mp hj
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (j.comm (q + 3) (q + 2))
      (PlaneProductTo.fullPlaneProductBoundaryChain m q B z)
    change (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (q + 3) (q + 2)
      (j.f (q + 3) (PlaneProductTo.fullPlaneProductBoundaryChain m q B z)) = _ at h
    rw [show j.f (q + 3) (PlaneProductTo.fullPlaneProductBoundaryChain m q B z) = _ from
      PlaneProductTo.fullPlaneProductBoundaryChain_is_cross_boundary m q B z hB] at h
    exact h.symm.trans (ConcreteCategory.congr_hom
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d_comp_d (q + 4) (q + 3) (q + 2))
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        2 (q + 2) (q + 4) (by omega) PlaneProductTo.rationalPlaneDiskFilling B))⟩

def fullPlaneProductRelativeCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m)))
      ({0}ᶜ)) (q + 4) :=
  Relative.FillingCycle.relativeFillingCycle ℚ (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ) (q + 3)
    (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
      2 (q + 2) (q + 4) (by omega) PlaneProductTo.rationalPlaneDiskFilling B)
    (fullPlaneProductBoundaryCycle m q B z hB)
    (PlaneProductTo.fullPlaneProductBoundaryChain_is_cross_boundary m q B z hB).symm

theorem fullPlaneProductRelativeCycle_boundary :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ
      (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).δ (q + 4) (q + 3) rfl
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (q + 4) (fullPlaneProductRelativeCycle m q B z hB)) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
        (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))))) (q + 3)
        (fullPlaneProductBoundaryCycle m q B z hB) :=
  Relative.FillingCycle.relativeFillingCycle_boundary ℚ (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ)
    (q + 3) (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
      2 (q + 2) (q + 4) (by omega) PlaneProductTo.rationalPlaneDiskFilling B)
    (fullPlaneProductBoundaryCycle m q B z hB)
    (PlaneProductTo.fullPlaneProductBoundaryChain_is_cross_boundary m q B z hB).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCycle
