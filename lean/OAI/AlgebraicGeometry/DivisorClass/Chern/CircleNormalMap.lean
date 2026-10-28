import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleArcWinding
import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalWinding

/-! # Circle Normal Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleNormalMap

noncomputable section

/-! The explicit positive real circle in the original complex normal line. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def circleNormalCoordinate : C(CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle, Fin 1 → ℂ) :=
  ⟨fun x _ => CircleArcWinding.circleComplexCoordinate x, continuous_pi fun _ => CircleArcWinding.circleComplexCoordinate.continuous⟩

theorem circleNormalCoordinate_norm (x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) : ‖circleNormalCoordinate x‖ = 1 := by
  change ‖fun _ : Fin 1 => CircleArcWinding.circleComplexCoordinate x‖ = 1
  rw [pi_norm_const]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map _).trans (norm_eq_of_mem_sphere x)

theorem circleNormalCoordinate_real (x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) :
    CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1 (circleNormalCoordinate x) = x.val := by
  have hre := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0)
    (Complex.orthonormalBasisOneI.repr.apply_symm_apply x.val)
  have him := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1)
    (Complex.orthonormalBasisOneI.repr.apply_symm_apply x.val)
  simp only [Complex.orthonormalBasisOneI_repr_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hre him
  ext i
  fin_cases i
  · change CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1 (circleNormalCoordinate x)
      (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexInterleavedIndex 1 (0, 0)) = _
    rw [CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv_apply_re]
    exact hre
  · change CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1 (circleNormalCoordinate x)
      (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexInterleavedIndex 1 (0, 1)) = _
    rw [CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv_apply_im]
    exact him

theorem circleNormalCoordinate_mem (x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) :
    circleNormalCoordinate x ∈ NormalWinding.windingNormalPunctured := by
  intro h
  exact CircleArcWinding.circleComplexCoordinate_ne_zero x (congrFun h 0)

def circleToNormalPunctured : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle ⟶ TopCat.of NormalWinding.windingNormalPunctured :=
  TopCat.ofHom ⟨fun x => ⟨circleNormalCoordinate x, circleNormalCoordinate_mem x⟩,
    circleNormalCoordinate.continuous.subtype_mk circleNormalCoordinate_mem⟩

theorem circleToNormalPunctured_radial (x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) :
    (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (Fin 1 → ℂ) (circleToNormalPunctured x)).val =
      circleNormalCoordinate x := by
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe]
  change ‖circleNormalCoordinate x‖⁻¹ • circleNormalCoordinate x = _
  rw [circleNormalCoordinate_norm, inv_one, one_smul]

/-- The original radial and interleaved real maps restore exactly the
original real circle, including its orientation. -/
theorem circleToNormalPunctured_real_radial :
    circleToNormalPunctured ≫ TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (Fin 1 → ℂ)) ≫
      TopCat.ofHom (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealSphereHomotopyEquiv 1).toFun = 𝟙 CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change ((CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealSphereHomotopyEquiv 1
    (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (Fin 1 → ℂ) (circleToNormalPunctured x))).val) = x.val
  rw [CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealSphereHomotopyEquiv_apply_coe, circleToNormalPunctured_radial,
    circleNormalCoordinate_real, norm_eq_of_mem_sphere x, inv_one, one_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleNormalMap
