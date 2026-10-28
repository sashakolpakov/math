import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere
import Mathlib.Analysis.Convex.Basic

/-! # Closed Ball Radial -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles

noncomputable section

/-!
# The complement of a closed coordinate ball

The actual inclusion of the complement of a nonnegative-radius closed ball
into the punctured vector space is a homotopy equivalence. Both composites
deform radially to the sphere of radius `r + 1`; the deformation stays outside
the closed ball when it starts there.
-/

open unitInterval

variable (E : Type*) [NormedAddCommGroup E]

/-- The actual complement of the closed ball centered at the origin. -/
abbrev OutsideClosedBall (r : ℝ) := (Metric.closedBall (0 : E) r)ᶜ

/-- Membership in the complement of a closed ball is the strict norm bound. -/
theorem outsideClosedBall_norm (r : ℝ) (x : OutsideClosedBall E r) :
    r < ‖(x : E)‖ := by
  simpa only [OutsideClosedBall, Set.mem_compl_iff, mem_closedBall_zero_iff,
    not_le] using x.property

/-- A point outside a closed ball of nonnegative radius is nonzero. -/
theorem outsideClosedBall_ne_zero (r : ℝ) (hr : 0 ≤ r) (x : OutsideClosedBall E r) :
    (x : E) ≠ 0 := by
  intro hx
  have hn := outsideClosedBall_norm E r x
  rw [hx, norm_zero] at hn
  exact (not_lt_of_ge hr) hn

/-- The actual inclusion of the closed-ball complement into the punctured space. -/
def outsideClosedBallInclusion (r : ℝ) (hr : 0 ≤ r) :
    C(OutsideClosedBall E r, NormalSphere.Cycles.PuncturedNormal E) where
  toFun x := ⟨x, outsideClosedBall_ne_zero E r hr x⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

variable [NormedSpace ℝ E]

private def interpolatePositiveRadius (a b : Set.Ioi (0 : ℝ)) (t : I) :
    Set.Ioi (0 : ℝ) :=
  ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ),
    (convex_Ioi (0 : ℝ)) a.property b.property (sub_nonneg.mpr t.property.2)
      t.property.1 (sub_add_cancel 1 (t : ℝ))⟩

private theorem polarPoint_norm (s : NormalSphere.Cycles.NormalUnitSphere E) (a : Set.Ioi (0 : ℝ)) :
    ‖((homeomorphUnitSphereProd E).symm (s, a) : E)‖ = (a : ℝ) := by
  rw [homeomorphUnitSphereProd_symm_apply_coe, norm_smul,
    Real.norm_of_nonneg a.property.le, mem_sphere_zero_iff_norm.mp s.property, mul_one]

/-- The radial map onto the sphere of a specified positive radius. -/
def normalRadiusMap (R : ℝ) (hR : 0 < R) : C(NormalSphere.Cycles.PuncturedNormal E, NormalSphere.Cycles.PuncturedNormal E) where
  toFun x := (homeomorphUnitSphereProd E).symm
    ((homeomorphUnitSphereProd E x).1, ⟨R, hR⟩)
  continuous_toFun := (homeomorphUnitSphereProd E).symm.continuous.comp
    (((homeomorphUnitSphereProd E).continuous.fst).prodMk continuous_const)

@[simp]
theorem normalRadiusMap_norm (R : ℝ) (hR : 0 < R) (x : NormalSphere.Cycles.PuncturedNormal E) :
    ‖(normalRadiusMap E R hR x : E)‖ = R :=
  polarPoint_norm E _ _

/-- Radial interpolation from a punctured point to the chosen-radius sphere. -/
def normalRadiusHomotopy (R : ℝ) (hR : 0 < R) :
    ContinuousMap.Homotopy (ContinuousMap.id (NormalSphere.Cycles.PuncturedNormal E))
      (normalRadiusMap E R hR) where
  toFun z := (homeomorphUnitSphereProd E).symm
    ((homeomorphUnitSphereProd E z.2).1,
      interpolatePositiveRadius (homeomorphUnitSphereProd E z.2).2 ⟨R, hR⟩ z.1)
  continuous_toFun := by
    apply (homeomorphUnitSphereProd E).symm.continuous.comp
    apply Continuous.prodMk
    · exact (homeomorphUnitSphereProd E).continuous.fst.comp continuous_snd
    · unfold interpolatePositiveRadius
      fun_prop
  map_zero_left x := by
    change (homeomorphUnitSphereProd E).symm
      ((homeomorphUnitSphereProd E x).1,
        interpolatePositiveRadius (homeomorphUnitSphereProd E x).2 ⟨R, hR⟩ 0) = x
    have h : interpolatePositiveRadius (homeomorphUnitSphereProd E x).2 ⟨R, hR⟩ 0 =
        (homeomorphUnitSphereProd E x).2 := by
      apply Subtype.ext
      simp [interpolatePositiveRadius]
    rw [h]
    exact (homeomorphUnitSphereProd E).symm_apply_apply x
  map_one_left x := by
    change (homeomorphUnitSphereProd E).symm
      ((homeomorphUnitSphereProd E x).1,
        interpolatePositiveRadius (homeomorphUnitSphereProd E x).2 ⟨R, hR⟩ 1) =
      (homeomorphUnitSphereProd E).symm ((homeomorphUnitSphereProd E x).1, ⟨R, hR⟩)
    have h : interpolatePositiveRadius (homeomorphUnitSphereProd E x).2 ⟨R, hR⟩ 1 =
        ⟨R, hR⟩ := by
      apply Subtype.ext
      simp [interpolatePositiveRadius]
    rw [h]

/-- The radial homotopy has precisely the linearly interpolated radius. -/
theorem normalRadiusHomotopy_norm (R : ℝ) (hR : 0 < R) (t : I) (x : NormalSphere.Cycles.PuncturedNormal E) :
    ‖(normalRadiusHomotopy E R hR (t, x) : E)‖ =
      (1 - (t : ℝ)) * ‖(x : E)‖ + (t : ℝ) * R := by
  change ‖((homeomorphUnitSphereProd E).symm
    ((homeomorphUnitSphereProd E x).1,
      interpolatePositiveRadius (homeomorphUnitSphereProd E x).2 ⟨R, hR⟩ t) : E)‖ = _
  rw [polarPoint_norm]
  simp only [interpolatePositiveRadius, homeomorphUnitSphereProd_apply_snd_coe]

private theorem normalRadiusMap_mem_outside (r : ℝ) (hr : 0 ≤ r)
    (x : NormalSphere.Cycles.PuncturedNormal E) :
    (normalRadiusMap E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one) x : E) ∈
      OutsideClosedBall E r := by
  simp only [OutsideClosedBall, Set.mem_compl_iff, mem_closedBall_zero_iff]
  rw [normalRadiusMap_norm]
  linarith

/-- Radial projection from the punctured space to the sphere of radius `r+1`,
viewed as a map into the complement of the closed radius-`r` ball. -/
def outsideClosedBallRetraction (r : ℝ) (hr : 0 ≤ r) :
    C(NormalSphere.Cycles.PuncturedNormal E, OutsideClosedBall E r) where
  toFun x := ⟨(normalRadiusMap E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one) x : E),
    normalRadiusMap_mem_outside E r hr x⟩
  continuous_toFun :=
    ((normalRadiusMap E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one)).continuous.subtype_val).subtype_mk
      (normalRadiusMap_mem_outside E r hr)

private theorem normalRadiusHomotopy_mem_outside (r : ℝ) (hr : 0 ≤ r)
    (z : I × OutsideClosedBall E r) :
    (normalRadiusHomotopy E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one)
      (z.1, outsideClosedBallInclusion E r hr z.2) : E) ∈ OutsideClosedBall E r := by
  simp only [OutsideClosedBall, Set.mem_compl_iff, mem_closedBall_zero_iff]
  rw [normalRadiusHomotopy_norm]
  apply not_le.mpr
  exact (convex_Ioi r) (outsideClosedBall_norm E r z.2)
    (show r < r + 1 by linarith) (sub_nonneg.mpr z.1.property.2)
    z.1.property.1 (sub_add_cancel 1 (z.1 : ℝ))

/-- The radial interpolation remains outside the closed ball at every time. -/
def outsideClosedBallHomotopy (r : ℝ) (hr : 0 ≤ r) :
    ContinuousMap.Homotopy (ContinuousMap.id (OutsideClosedBall E r))
      ((outsideClosedBallRetraction E r hr).comp (outsideClosedBallInclusion E r hr)) where
  toFun z := ⟨normalRadiusHomotopy E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one)
    (z.1, outsideClosedBallInclusion E r hr z.2), normalRadiusHomotopy_mem_outside E r hr z⟩
  continuous_toFun :=
    (((normalRadiusHomotopy E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one)).continuous.comp
      (continuous_fst.prodMk ((outsideClosedBallInclusion E r hr).continuous.comp
        continuous_snd))).subtype_val).subtype_mk (normalRadiusHomotopy_mem_outside E r hr)
  map_zero_left x := by
    apply Subtype.ext
    exact congrArg (fun v : NormalSphere.Cycles.PuncturedNormal E => (v : E))
      ((normalRadiusHomotopy E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one)).map_zero_left
        (outsideClosedBallInclusion E r hr x))
  map_one_left x := by
    apply Subtype.ext
    exact congrArg (fun v : NormalSphere.Cycles.PuncturedNormal E => (v : E))
      ((normalRadiusHomotopy E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one)).map_one_left
        (outsideClosedBallInclusion E r hr x))

/-- The actual inclusion from the complement of a closed ball into the
punctured vector space is a homotopy equivalence. -/
def outsideClosedBallHomotopyEquiv (r : ℝ) (hr : 0 ≤ r) :
    ContinuousMap.HomotopyEquiv (OutsideClosedBall E r) (NormalSphere.Cycles.PuncturedNormal E) where
  toFun := outsideClosedBallInclusion E r hr
  invFun := outsideClosedBallRetraction E r hr
  left_inv := ⟨(outsideClosedBallHomotopy E r hr).symm⟩
  right_inv := ⟨(normalRadiusHomotopy E (r + 1) (lt_add_of_le_of_pos hr zero_lt_one)).symm⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial.Cycles
