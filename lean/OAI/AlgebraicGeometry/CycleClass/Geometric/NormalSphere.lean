import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Homotopy.Equiv

/-! # Normal Sphere -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere.Cycles

noncomputable section

/-!
# The sphere in a punctured normal space

Radial normalization is a strong deformation retraction from a punctured real
normed vector space to its unit sphere. This applies in particular to the real
normed space underlying a complex normal coordinate space. The construction
uses mathlib's actual polar-coordinate homeomorphism; it makes no assertion
about sphere homology or the existence of a Thom class.
-/

open unitInterval

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complement of the origin in a normal coordinate vector space. -/
abbrev PuncturedNormal := ({0}ᶜ : Set E)

/-- The actual unit sphere of a normal coordinate vector space. -/
abbrev NormalUnitSphere := Metric.sphere (0 : E) 1

private def radiusOne : Set.Ioi (0 : ℝ) := ⟨1, by change (0 : ℝ) < 1; exact zero_lt_one⟩

/-- Radial projection to the sphere in polar coordinates. -/
def normalSphereProjection : C(PuncturedNormal E, NormalUnitSphere E) where
  toFun x := (homeomorphUnitSphereProd E x).1
  continuous_toFun := (homeomorphUnitSphereProd E).continuous.fst

/-- Inclusion of the unit sphere into the punctured normal space. -/
def normalSphereInclusion : C(NormalUnitSphere E, PuncturedNormal E) where
  toFun x := (homeomorphUnitSphereProd E).symm (x, radiusOne)
  continuous_toFun := (homeomorphUnitSphereProd E).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

@[simp]
theorem normalSphereProjection_coe (x : PuncturedNormal E) :
    ((normalSphereProjection E x : NormalUnitSphere E) : E) = ‖(x : E)‖⁻¹ • (x : E) := by
  simp [normalSphereProjection, homeomorphUnitSphereProd_apply_fst_coe]

@[simp]
theorem normalSphereInclusion_coe (x : NormalUnitSphere E) :
    ((normalSphereInclusion E x : PuncturedNormal E) : E) = (x : E) := by
  simp [normalSphereInclusion, homeomorphUnitSphereProd_symm_apply_coe, radiusOne]

@[simp]
theorem normalSphereProjection_inclusion (x : NormalUnitSphere E) :
    normalSphereProjection E (normalSphereInclusion E x) = x := by
  change ((homeomorphUnitSphereProd E)
    ((homeomorphUnitSphereProd E).symm (x, radiusOne))).1 = x
  rw [(homeomorphUnitSphereProd E).apply_symm_apply]

private def interpolateRadius (t : I) (r : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(1 - (t : ℝ)) * (r : ℝ) + (t : ℝ), by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hr : 0 < (r : ℝ) := r.property
    rcases lt_or_eq_of_le ht0 with ht | ht
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hr.le) ht
    · simp [← ht]⟩

private theorem continuous_interpolateRadius :
    Continuous (fun z : I × Set.Ioi (0 : ℝ) => interpolateRadius z.1 z.2) := by
  unfold interpolateRadius
  fun_prop

@[simp]
private theorem interpolateRadius_zero (r : Set.Ioi (0 : ℝ)) :
    interpolateRadius 0 r = r := by
  apply Subtype.ext
  simp [interpolateRadius]

@[simp]
private theorem interpolateRadius_one (r : Set.Ioi (0 : ℝ)) :
    interpolateRadius 1 r = radiusOne := by
  apply Subtype.ext
  simp [interpolateRadius, radiusOne]

@[simp]
private theorem interpolateRadius_radiusOne (t : I) :
    interpolateRadius t radiusOne = radiusOne := by
  apply Subtype.ext
  simp [interpolateRadius, radiusOne]

/-- Radial contraction to the unit sphere, fixed at every point of that sphere
throughout the homotopy. The radius changes from `r` to `(1-t)*r+t`. -/
def normalSphereDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PuncturedNormal E))
      ((normalSphereInclusion E).comp (normalSphereProjection E))
      (Set.range (normalSphereInclusion E)) where
  toFun z := (homeomorphUnitSphereProd E).symm
    ((homeomorphUnitSphereProd E z.2).1,
      interpolateRadius z.1 (homeomorphUnitSphereProd E z.2).2)
  continuous_toFun := (homeomorphUnitSphereProd E).symm.continuous.comp
    (((homeomorphUnitSphereProd E).continuous.fst.comp continuous_snd).prodMk
      (continuous_interpolateRadius.comp
        (continuous_fst.prodMk ((homeomorphUnitSphereProd E).continuous.snd.comp continuous_snd))))
  map_zero_left x := by
    change (homeomorphUnitSphereProd E).symm
      ((homeomorphUnitSphereProd E x).1,
        interpolateRadius 0 (homeomorphUnitSphereProd E x).2) = x
    rw [interpolateRadius_zero]
    exact (homeomorphUnitSphereProd E).symm_apply_apply x
  map_one_left x := by
    change (homeomorphUnitSphereProd E).symm
      ((homeomorphUnitSphereProd E x).1,
        interpolateRadius 1 (homeomorphUnitSphereProd E x).2) =
      (homeomorphUnitSphereProd E).symm ((homeomorphUnitSphereProd E x).1, radiusOne)
    rw [interpolateRadius_one]
  prop' t x hx := by
    rcases hx with ⟨y, rfl⟩
    change (homeomorphUnitSphereProd E).symm
      (((homeomorphUnitSphereProd E) ((homeomorphUnitSphereProd E).symm (y, radiusOne))).1,
        interpolateRadius t
          (((homeomorphUnitSphereProd E) ((homeomorphUnitSphereProd E).symm (y, radiusOne))).2)) =
      (homeomorphUnitSphereProd E).symm (y, radiusOne)
    rw [(homeomorphUnitSphereProd E).apply_symm_apply]
    simp only [interpolateRadius_radiusOne]

/-- The radial deformation has the usual positive scalar interpolation formula. -/
theorem normalSphereDeformation_coe (t : I) (x : PuncturedNormal E) :
    (((normalSphereDeformation E) (t, x) : PuncturedNormal E) : E) =
      (((1 - (t : ℝ)) * ‖(x : E)‖ + (t : ℝ)) / ‖(x : E)‖) • (x : E) := by
  change (((homeomorphUnitSphereProd E).symm
    ((homeomorphUnitSphereProd E x).1,
      interpolateRadius t (homeomorphUnitSphereProd E x).2) : PuncturedNormal E) : E) = _
  rw [homeomorphUnitSphereProd_symm_apply_coe]
  simp only [interpolateRadius, homeomorphUnitSphereProd_apply_fst_coe,
    homeomorphUnitSphereProd_apply_snd_coe, smul_smul, div_eq_mul_inv]

@[simp]
theorem normalSphereDeformation_fixed (t : I) (x : NormalUnitSphere E) :
    (normalSphereDeformation E) (t, normalSphereInclusion E x) = normalSphereInclusion E x := by
  exact (normalSphereDeformation E).eq_fst t (Set.mem_range_self x)

/-- The punctured normal coordinate space and its unit sphere are homotopy
equivalent, via the explicit radial deformation retraction. -/
def normalSphereHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (PuncturedNormal E) (NormalUnitSphere E) where
  toFun := normalSphereProjection E
  invFun := normalSphereInclusion E
  left_inv := ⟨(normalSphereDeformation E).toHomotopy.symm⟩
  right_inv := by
    have h : (normalSphereProjection E).comp (normalSphereInclusion E) =
        ContinuousMap.id (NormalUnitSphere E) := by
      apply ContinuousMap.ext
      intro x
      exact normalSphereProjection_inclusion E x
    rw [h]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere.Cycles
