import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology

/-! # Circle Equator Orientation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleEquatorOrientation

noncomputable section

section

/-!
# ChernClass: the actual ordered equator coordinate in the circle normalization

The repaired sphere constructor drops the north-pole coordinate and keeps
the remaining real coordinates in their original order. Its circle basis
sends the positive imaginary direction to positive one.
-/

open OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev CircleEquator := CycleClass.Geometric.SphereCover.Cycles.SphereEquatorSpace (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1)

/-- The positive imaginary axis inside the literal real equatorial line. -/
def positiveCircleEquator : CircleEquator :=
  ⟨EuclideanSpace.single (1 : Fin 2) 1, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole, EuclideanSpace.inner_single_left]⟩

theorem positiveCircleEquator_norm : ‖positiveCircleEquator‖ = 1 := by
  change ‖EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ = 1
  simp

/-- The exact basis used in the existing circle-overlap normalization. -/
def chosenCircleEquatorBasis : OrthonormalBasis (Fin 1) ℝ CircleEquator :=
  CycleClass.Geometric.SphereCover.Cycles.orderedEquatorBasis 1

/-- Its coordinate of the positive imaginary direction. -/
def chosenCircleEquatorSign : ℝ := chosenCircleEquatorBasis.repr positiveCircleEquator 0

/-- The actual repaired constructor fixes the positive complex orientation. -/
theorem chosenCircleEquatorSign_eq_one : chosenCircleEquatorSign = 1 := by
  change (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 = 1
  simp

/-- Every orthonormal coordinate of this real equatorial line retains
exactly a sign ambiguity on the explicit positive imaginary unit. -/
theorem circleEquator_coordinate_eq_one_or_neg_one (b : OrthonormalBasis (Fin 1) ℝ CircleEquator) :
    b.repr positiveCircleEquator 0 = 1 ∨ b.repr positiveCircleEquator 0 = -1 := by
  have h : ‖b.repr positiveCircleEquator‖ = 1 :=
    (b.repr.norm_map _).trans positiveCircleEquator_norm
  have hv : b.repr positiveCircleEquator =
      EuclideanSpace.single (0 : Fin 1) (b.repr positiveCircleEquator 0) := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [hv] at h
  simpa only [PiLp.norm_single, Real.norm_eq_abs, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] using h

theorem chosenCircleEquatorSign_eq_one_or_neg_one :
    chosenCircleEquatorSign = 1 ∨ chosenCircleEquatorSign = -1 :=
  circleEquator_coordinate_eq_one_or_neg_one chosenCircleEquatorBasis

/-- Reversing the real equator basis preserves orthonormality and
reverses its coordinate on the same positive imaginary unit. -/
theorem circleEquator_negatedBasis_coordinate (b : OrthonormalBasis (Fin 1) ℝ CircleEquator) :
    (b.map (LinearIsometryEquiv.neg ℝ)).repr positiveCircleEquator 0 =
      -(b.repr positiveCircleEquator 0) := by
  change b.repr (-positiveCircleEquator) 0 = _
  rw [map_neg]
  rfl

/-- The orthonormal-basis requirements themselves admit both signs on
the explicit positive imaginary direction. -/
theorem circleEquator_both_coordinate_signs :
    (∃ b : OrthonormalBasis (Fin 1) ℝ CircleEquator, b.repr positiveCircleEquator 0 = 1) ∧
      (∃ b : OrthonormalBasis (Fin 1) ℝ CircleEquator, b.repr positiveCircleEquator 0 = -1) := by
  let b := chosenCircleEquatorBasis
  have hn := circleEquator_negatedBasis_coordinate b
  rcases circleEquator_coordinate_eq_one_or_neg_one b with hp | hm
  · exact ⟨⟨b, hp⟩, ⟨b.map (LinearIsometryEquiv.neg ℝ), hn.trans (congrArg Neg.neg hp)⟩⟩
  · refine ⟨⟨b.map (LinearIsometryEquiv.neg ℝ), ?_⟩, ⟨b, hm⟩⟩
    simpa only [hm, neg_neg] using hn

end

/-!
# ChernClass: the positive imaginary point through the original circle overlap map

The actual stereographic and radial maps send the positive imaginary unit
to the positive equatorial unit. The final real coordinate is exactly the
chosen equator basis coordinate identified in the preceding module.
-/

open OAI.AlgebraicGeometry.CycleClass.Geometric.SmallCircleHomology.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The actual positive imaginary point of the real coordinate circle. -/
def positiveCirclePoint : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle :=
  ⟨EuclideanSpace.single (1 : Fin 2) 1, by simp [CycleClass.Geometric.NormalSphere.Cycles.NormalUnitSphere]⟩

theorem positiveCirclePoint_firstChart : positiveCirclePoint ∈ CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart := by
  intro h
  have hc := congrArg (fun x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle => x.val (0 : Fin 2)) h
  simp [positiveCirclePoint, CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at hc

theorem positiveCirclePoint_secondChart : positiveCirclePoint ∈ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart := by
  intro h
  have hc := congrArg (fun x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle => x.val (0 : Fin 2)) h
  simp [positiveCirclePoint, CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at hc

def positiveCircleOverlap : CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap :=
  ⟨positiveCirclePoint, positiveCirclePoint_firstChart, positiveCirclePoint_secondChart⟩

/-- The original stereographic coordinate is twice the positive imaginary unit. -/
theorem positiveCircleOverlap_stereographic :
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) positiveCircleOverlap : CircleEquator) =
      (2 : ℝ) • positiveCircleEquator := by
  rw [CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart_apply, stereographic_apply]
  have hi : inner ℝ (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1 : EuclideanSpace ℝ (Fin 2))
      (positiveCirclePoint : EuclideanSpace ℝ (Fin 2)) = 0 := by
    simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole, positiveCirclePoint, EuclideanSpace.inner_single_left]
  have he : (positiveCirclePoint : EuclideanSpace ℝ (Fin 2)) =
      (positiveCircleEquator : EuclideanSpace ℝ (Fin 2)) := rfl
  change (2 / (1 - inner ℝ (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1 : EuclideanSpace ℝ (Fin 2))
      (positiveCirclePoint : EuclideanSpace ℝ (Fin 2)))) •
      (CycleClass.Geometric.SphereCover.Cycles.SphereEquatorSpace (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1)).orthogonalProjectionOnto
        (positiveCirclePoint : EuclideanSpace ℝ (Fin 2)) = _
  rw [hi, he, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  norm_num

/-- Radial normalization restores precisely the original positive equatorial unit. -/
theorem positiveCircleOverlap_radial :
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionSphereEquiv (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) positiveCircleOverlap : CircleEquator) =
      positiveCircleEquator := by
  change (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection CircleEquator
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) positiveCircleOverlap) : CircleEquator) = _
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe, positiveCircleOverlap_stereographic,
    norm_smul, positiveCircleEquator_norm, smul_smul]
  norm_num

/-- The actual lower-sphere map uses exactly the chosen real equator sign. -/
theorem positiveCircleOverlap_lowerSphere_coordinate :
    (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv 1 positiveCircleOverlap : EuclideanSpace ℝ (Fin 1)) 0 =
      chosenCircleEquatorSign := by
  change chosenCircleEquatorBasis.repr
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionSphereEquiv (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) positiveCircleOverlap) 0 = _
  rw [positiveCircleOverlap_radial]
  rfl

/-- The original labelled zero-sphere value at the positive imaginary
point is precisely the same real basis sign. -/
theorem positiveCircleOverlap_zeroSphere_value :
    (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlapZeroSphereEquiv positiveCircleOverlap) : ℝ) =
      chosenCircleEquatorSign := by
  change (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph (CycleClass.Geometric.ZeroSphere.Cycles.zeroSphereRealHomeomorph.symm
    (CycleClass.Geometric.SmallCircleHomology.Cycles.euclideanLineSphereHomeomorph (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv 1 positiveCircleOverlap))) : ℝ) = _
  rw [Homeomorph.apply_symm_apply]
  change (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv 1 positiveCircleOverlap) = _
  rw [← OrthonormalBasis.sum_repr_symm]
  simpa using positiveCircleOverlap_lowerSphere_coordinate

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleEquatorOrientation
