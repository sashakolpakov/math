import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleArcWinding

/-! # Circle Overlap Labels -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOverlapLabels

noncomputable section

/-! The original zero-sphere labels of the two imaginary circle points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem negativeCircleOverlap_stereographic :
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) CircleArcWinding.negativeCircleOverlap : CircleEquatorOrientation.CircleEquator) =
      (2 : ℝ) • (-CircleEquatorOrientation.positiveCircleEquator) := by
  rw [CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart_apply, stereographic_apply]
  have hi : inner ℝ (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1 : EuclideanSpace ℝ (Fin 2))
      (-CircleEquatorOrientation.positiveCirclePoint : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle).val = 0 := by
    simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole, CircleEquatorOrientation.positiveCirclePoint, EuclideanSpace.inner_single_left]
  have he : (-CircleEquatorOrientation.positiveCirclePoint : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle).val =
      ((-CircleEquatorOrientation.positiveCircleEquator : CircleEquatorOrientation.CircleEquator) : EuclideanSpace ℝ (Fin 2)) := rfl
  change (2 / (1 - inner ℝ (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1 : EuclideanSpace ℝ (Fin 2))
      (-CircleEquatorOrientation.positiveCirclePoint : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle).val)) •
      (CycleClass.Geometric.SphereCover.Cycles.SphereEquatorSpace (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1)).orthogonalProjectionOnto
        (-CircleEquatorOrientation.positiveCirclePoint : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle).val = _
  rw [hi, he, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  norm_num

theorem negativeCircleOverlap_radial :
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionSphereEquiv (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) CircleArcWinding.negativeCircleOverlap : CircleEquatorOrientation.CircleEquator) =
      -CircleEquatorOrientation.positiveCircleEquator := by
  change (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection CircleEquatorOrientation.CircleEquator
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) CircleArcWinding.negativeCircleOverlap) : CircleEquatorOrientation.CircleEquator) = _
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe, negativeCircleOverlap_stereographic,
    norm_smul, norm_neg, CircleEquatorOrientation.positiveCircleEquator_norm, smul_smul]
  norm_num

theorem negativeCircleOverlap_lowerSphere_coordinate :
    (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv 1 CircleArcWinding.negativeCircleOverlap : EuclideanSpace ℝ (Fin 1)) 0 =
      -CircleEquatorOrientation.chosenCircleEquatorSign := by
  change CircleEquatorOrientation.chosenCircleEquatorBasis.repr
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionSphereEquiv (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) CircleArcWinding.negativeCircleOverlap) 0 = _
  rw [negativeCircleOverlap_radial, map_neg]
  rfl

theorem negativeCircleOverlap_zeroSphere_value :
    (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv CircleArcWinding.negativeCircleOverlap) : ℝ) =
      -CircleEquatorOrientation.chosenCircleEquatorSign := by
  change (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph.symm
    (CycleClass.Geometric.SmallCircleHomology.Cycles.euclideanLineSphereHomeomorph (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv 1 CircleArcWinding.negativeCircleOverlap))) : ℝ) = _
  rw [Homeomorph.apply_symm_apply]
  change (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv 1 CircleArcWinding.negativeCircleOverlap) = _
  rw [← OrthonormalBasis.sum_repr_symm]
  simpa using negativeCircleOverlap_lowerSphere_coordinate

theorem positiveCircleOverlap_label_of_positive (h : CircleEquatorOrientation.chosenCircleEquatorSign = 1) :
    CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv CircleEquatorOrientation.positiveCircleOverlap = 1 := by
  apply CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph.injective
  apply Subtype.ext
  rw [CircleEquatorOrientation.positiveCircleOverlap_zeroSphere_value, h]
  rfl

theorem negativeCircleOverlap_label_of_positive (h : CircleEquatorOrientation.chosenCircleEquatorSign = 1) :
    CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv CircleArcWinding.negativeCircleOverlap = 0 := by
  apply CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph.injective
  apply Subtype.ext
  rw [negativeCircleOverlap_zeroSphere_value, h]
  rfl

theorem positiveCircleOverlap_label_of_negative (h : CircleEquatorOrientation.chosenCircleEquatorSign = -1) :
    CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv CircleEquatorOrientation.positiveCircleOverlap = 0 := by
  apply CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph.injective
  apply Subtype.ext
  rw [CircleEquatorOrientation.positiveCircleOverlap_zeroSphere_value, h]
  rfl

theorem negativeCircleOverlap_label_of_negative (h : CircleEquatorOrientation.chosenCircleEquatorSign = -1) :
    CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv CircleArcWinding.negativeCircleOverlap = 1 := by
  apply CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph.injective
  apply Subtype.ext
  rw [negativeCircleOverlap_zeroSphere_value, h, neg_neg]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOverlapLabels
