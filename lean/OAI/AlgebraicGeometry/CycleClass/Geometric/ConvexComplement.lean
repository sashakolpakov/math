import OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBallRadial
import Mathlib.Topology.MetricSpace.Bounded

/-! # Convex Complement -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ConvexComplement.Cycles

noncomputable section

/-!
# Complements of compact convex sets

The inclusion of the complement of a compact convex set into the complement
of any one of its points is a genuine homotopy equivalence. An explicit
radial map about that point takes values on a sphere strictly enclosing the
set. The homotopies interpolate the radius and stay in the required
complements. No nonemptiness assumption on a sphere or a complement is used.
-/

open unitInterval

variable {E : Type*}

/-- A point outside a set differs from every specified point of the set. -/
theorem convexComplement_ne_point (K : Set E) (x : E) (hx : x ∈ K)
    (y : ↥(Kᶜ)) : (y : E) ≠ x := by
  intro h
  apply y.property
  simpa only [h] using hx

variable [NormedAddCommGroup E]

/-- The literal inclusion of the complement of a set into a point complement. -/
def convexComplementInclusion (K : Set E) (x : E) (hx : x ∈ K) :
    C(↥(Kᶜ), ↥(({x} : Set E)ᶜ)) where
  toFun y := ⟨y, convexComplement_ne_point K x hx y⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (convexComplement_ne_point K x hx)

@[simp]
theorem convexComplementInclusion_coe (K : Set E) (x : E) (hx : x ∈ K)
    (y : ↥(Kᶜ)) : (convexComplementInclusion K x hx y : E) = y := rfl

/-- Translation from a punctured space centered at `x` to the punctured vector space. -/
def puncturedPointToOrigin (x : E) : C(↥(({x} : Set E)ᶜ), NormalSphere.Cycles.PuncturedNormal E) where
  toFun y := ⟨(y : E) - x, sub_ne_zero.mpr y.property⟩
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

theorem puncturedOrigin_add_ne (x : E) (y : NormalSphere.Cycles.PuncturedNormal E) : (y : E) + x ≠ x := by
  intro h
  apply y.property
  simpa using congrArg (fun z : E => z - x) h

/-- Inverse translation from the punctured vector space. -/
def puncturedOriginToPoint (x : E) : C(NormalSphere.Cycles.PuncturedNormal E, ↥(({x} : Set E)ᶜ)) where
  toFun y := ⟨(y : E) + x, puncturedOrigin_add_ne x y⟩
  continuous_toFun :=
    (continuous_subtype_val.add continuous_const).subtype_mk (puncturedOrigin_add_ne x)

@[simp]
theorem puncturedOriginToPoint_toOrigin (x : E) (y : ↥(({x} : Set E)ᶜ)) :
    puncturedOriginToPoint x (puncturedPointToOrigin x y) = y := by
  apply Subtype.ext
  exact sub_add_cancel _ _

variable [NormedSpace ℝ E]

/-- The positive-radius projection centered at the specified point. -/
def puncturedPointRadiusMap (x : E) (R : ℝ) (hR : 0 < R) :
    C(↥(({x} : Set E)ᶜ), ↥(({x} : Set E)ᶜ)) :=
  (puncturedOriginToPoint x).comp ((ClosedBallRadial.Cycles.normalRadiusMap E R hR).comp (puncturedPointToOrigin x))

/-- Radial interpolation centered at `x`, on the actual point complement. -/
def puncturedPointRadiusHomotopy (x : E) (R : ℝ) (hR : 0 < R) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(({x} : Set E)ᶜ))
      (puncturedPointRadiusMap x R hR) where
  toFun z := puncturedOriginToPoint x
    (ClosedBallRadial.Cycles.normalRadiusHomotopy E R hR (z.1, puncturedPointToOrigin x z.2))
  continuous_toFun := (puncturedOriginToPoint x).continuous.comp
    ((ClosedBallRadial.Cycles.normalRadiusHomotopy E R hR).continuous.comp
      (continuous_fst.prodMk ((puncturedPointToOrigin x).continuous.comp continuous_snd)))
  map_zero_left y := by
    exact (congrArg (fun z : NormalSphere.Cycles.PuncturedNormal E => puncturedOriginToPoint x z)
      ((ClosedBallRadial.Cycles.normalRadiusHomotopy E R hR).map_zero_left (puncturedPointToOrigin x y))).trans
        (puncturedOriginToPoint_toOrigin x y)
  map_one_left y := by
    exact congrArg (fun z : NormalSphere.Cycles.PuncturedNormal E => puncturedOriginToPoint x z)
      ((ClosedBallRadial.Cycles.normalRadiusHomotopy E R hR).map_one_left (puncturedPointToOrigin x y))

/-- The radial projection is on the sphere of radius `R` about `x`. -/
theorem puncturedPointRadiusMap_dist (x : E) (R : ℝ) (hR : 0 < R)
    (y : ↥(({x} : Set E)ᶜ)) :
    dist (puncturedPointRadiusMap x R hR y : E) x = R := by
  change dist ((ClosedBallRadial.Cycles.normalRadiusMap E R hR (puncturedPointToOrigin x y) : E) + x) x = R
  simpa only [dist_eq_norm, add_sub_cancel_right] using
    ClosedBallRadial.Cycles.normalRadiusMap_norm E R hR (puncturedPointToOrigin x y)

/-- The interpolated distance is the convex combination of the two radii. -/
theorem puncturedPointRadiusHomotopy_dist (x : E) (R : ℝ) (hR : 0 < R)
    (t : I) (y : ↥(({x} : Set E)ᶜ)) :
    dist (puncturedPointRadiusHomotopy x R hR (t, y) : E) x =
      (1 - (t : ℝ)) * dist (y : E) x + (t : ℝ) * R := by
  change dist ((ClosedBallRadial.Cycles.normalRadiusHomotopy E R hR (t, puncturedPointToOrigin x y) : E) + x) x = _
  simp only [dist_eq_norm, add_sub_cancel_right]
  exact ClosedBallRadial.Cycles.normalRadiusHomotopy_norm E R hR t (puncturedPointToOrigin x y)

/-- The existing polar-coordinate interpolation has the usual scalar formula. -/
theorem normalRadiusHomotopy_coe (R : ℝ) (hR : 0 < R) (t : I)
    (y : NormalSphere.Cycles.PuncturedNormal E) :
    (ClosedBallRadial.Cycles.normalRadiusHomotopy E R hR (t, y) : E) =
      (((1 - (t : ℝ)) * ‖(y : E)‖ + (t : ℝ) * R) / ‖(y : E)‖) • (y : E) := by
  change ((1 - (t : ℝ)) * ((homeomorphUnitSphereProd E y).2 : ℝ) + (t : ℝ) * R) •
      ((homeomorphUnitSphereProd E y).1 : E) = _
  simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe,
    smul_smul, div_eq_mul_inv]

/-- Radial interpolation about `x` moves along the ray through its argument. -/
theorem puncturedPointRadiusHomotopy_coe (x : E) (R : ℝ) (hR : 0 < R)
    (t : I) (y : ↥(({x} : Set E)ᶜ)) :
    (puncturedPointRadiusHomotopy x R hR (t, y) : E) =
      (((1 - (t : ℝ)) * ‖(y : E) - x‖ + (t : ℝ) * R) / ‖(y : E) - x‖) •
        ((y : E) - x) + x := by
  change (ClosedBallRadial.Cycles.normalRadiusHomotopy E R hR (t, puncturedPointToOrigin x y) : E) + x = _
  rw [normalRadiusHomotopy_coe]
  rfl

/-- Once a ray from a point of a convex set has left the set, all farther
points of that ray remain outside. -/
theorem convex_ray_not_mem {K : Set E} (hK : Convex ℝ K) {x y : E}
    (hx : x ∈ K) (hy : y ∉ K) {a : ℝ} (ha : 1 ≤ a) :
    a • (y - x) + x ∉ K := by
  intro hz
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hmem := hK.add_smul_sub_mem hx hz
    (show a⁻¹ ∈ Set.Icc (0 : ℝ) 1 from
      ⟨inv_nonneg.mpr hapos.le, (inv_le_one₀ hapos).mpr ha⟩)
  apply hy
  simpa [smul_smul, hapos.ne', add_comm] using hmem

/-- A radial projection onto a sphere strictly enclosing `K` lies outside `K`. -/
theorem puncturedPointRadiusMap_not_mem (K : Set E) (x : E) (R : ℝ) (hR : 0 < R)
    (hbound : K ⊆ Metric.ball x R) (y : ↥(({x} : Set E)ᶜ)) :
    (puncturedPointRadiusMap x R hR y : E) ∉ K := by
  intro hy
  have hlt := Metric.mem_ball.mp (hbound hy)
  rw [puncturedPointRadiusMap_dist] at hlt
  exact lt_irrefl R hlt

/-- The radial interpolation remains outside a convex set containing its center. -/
theorem puncturedPointRadiusHomotopy_not_mem (K : Set E) (x : E)
    (hconv : Convex ℝ K) (hx : x ∈ K) (R : ℝ) (hR : 0 < R)
    (hbound : K ⊆ Metric.ball x R) (t : I) (y : ↥(Kᶜ)) :
    (puncturedPointRadiusHomotopy x R hR
      (t, convexComplementInclusion K x hx y) : E) ∉ K := by
  have hnorm : 0 < ‖(y : E) - x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (convexComplement_ne_point K x hx y))
  by_cases hsmall : ‖(y : E) - x‖ ≤ R
  · rw [puncturedPointRadiusHomotopy_coe]
    apply convex_ray_not_mem hconv hx y.property
    apply (one_le_div hnorm).mpr
    have ht := t.property.1
    have hmul := mul_nonneg ht (sub_nonneg.mpr hsmall)
    change ‖(y : E) - x‖ ≤ (1 - (t : ℝ)) * ‖(y : E) - x‖ + (t : ℝ) * R
    nlinarith
  · have hlarge : R ≤ dist (y : E) x := by
      rw [dist_eq_norm]
      exact le_of_lt (lt_of_not_ge hsmall)
    have hdist : R ≤ dist (puncturedPointRadiusHomotopy x R hR
        (t, convexComplementInclusion K x hx y) : E) x := by
      rw [puncturedPointRadiusHomotopy_dist]
      change R ≤ (1 - (t : ℝ)) * dist (y : E) x + (t : ℝ) * R
      have hmul := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hlarge)
      nlinarith
    intro hy
    exact (not_lt_of_ge hdist) (Metric.mem_ball.mp (hbound hy))

/-- The explicit homotopy inverse sends each punctured point to the enclosing sphere. -/
def convexComplementRetractionOfRadius (K : Set E) (x : E) (R : ℝ) (hR : 0 < R)
    (hbound : K ⊆ Metric.ball x R) : C(↥(({x} : Set E)ᶜ), ↥(Kᶜ)) where
  toFun y := ⟨puncturedPointRadiusMap x R hR y,
    puncturedPointRadiusMap_not_mem K x R hR hbound y⟩
  continuous_toFun := ((puncturedPointRadiusMap x R hR).continuous.subtype_val).subtype_mk
    (puncturedPointRadiusMap_not_mem K x R hR hbound)

/-- Restriction of the explicit radial homotopy to the complement of `K`. -/
def convexComplementHomotopyOfRadius (K : Set E) (x : E)
    (hconv : Convex ℝ K) (hx : x ∈ K) (R : ℝ) (hR : 0 < R)
    (hbound : K ⊆ Metric.ball x R) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(Kᶜ))
      ((convexComplementRetractionOfRadius K x R hR hbound).comp
        (convexComplementInclusion K x hx)) where
  toFun z := ⟨puncturedPointRadiusHomotopy x R hR
    (z.1, convexComplementInclusion K x hx z.2),
    puncturedPointRadiusHomotopy_not_mem K x hconv hx R hR hbound z.1 z.2⟩
  continuous_toFun :=
    (((puncturedPointRadiusHomotopy x R hR).continuous.comp
      (continuous_fst.prodMk ((convexComplementInclusion K x hx).continuous.comp
        continuous_snd))).subtype_val).subtype_mk
      (fun z => puncturedPointRadiusHomotopy_not_mem K x hconv hx R hR hbound z.1 z.2)
  map_zero_left y := by
    apply Subtype.ext
    exact congrArg (fun z : ↥(({x} : Set E)ᶜ) => (z : E))
      ((puncturedPointRadiusHomotopy x R hR).map_zero_left
        (convexComplementInclusion K x hx y))
  map_one_left y := by
    apply Subtype.ext
    exact congrArg (fun z : ↥(({x} : Set E)ᶜ) => (z : E))
      ((puncturedPointRadiusHomotopy x R hR).map_one_left
        (convexComplementInclusion K x hx y))

/-- The actual complement inclusion is a homotopy equivalence whenever a
positive-radius ball strictly contains the convex set. -/
def convexComplementHomotopyEquivOfRadius (K : Set E) (x : E)
    (hconv : Convex ℝ K) (hx : x ∈ K) (R : ℝ) (hR : 0 < R)
    (hbound : K ⊆ Metric.ball x R) :
    ContinuousMap.HomotopyEquiv ↥(Kᶜ) ↥(({x} : Set E)ᶜ) where
  toFun := convexComplementInclusion K x hx
  invFun := convexComplementRetractionOfRadius K x R hR hbound
  left_inv := ⟨(convexComplementHomotopyOfRadius K x hconv hx R hR hbound).symm⟩
  right_inv := ⟨(puncturedPointRadiusHomotopy x R hR).symm⟩

/-- For a compact convex set and any point in it, the literal inclusion of
its complement into that point's complement is a homotopy equivalence.
This holds in every real normed space, including the zero-dimensional case. -/
def convexComplementHomotopyEquiv (K : Set E) (x : E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hx : x ∈ K) :
    ContinuousMap.HomotopyEquiv ↥(Kᶜ) ↥(({x} : Set E)ᶜ) := by
  let R := Classical.choose (hK.isBounded.subset_ball_lt 0 x)
  have hR : 0 < R := (Classical.choose_spec (hK.isBounded.subset_ball_lt 0 x)).1
  have hbound : K ⊆ Metric.ball x R := (Classical.choose_spec (hK.isBounded.subset_ball_lt 0 x)).2
  exact convexComplementHomotopyEquivOfRadius K x hconv hx R hR hbound

/-- The forward map is precisely the original inclusion, not an independently
chosen homotopy-equivalent map. -/
@[simp]
theorem convexComplementHomotopyEquiv_toFun (K : Set E) (x : E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hx : x ∈ K) :
    (convexComplementHomotopyEquiv K x hK hconv hx).toFun =
      convexComplementInclusion K x hx := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ConvexComplement.Cycles
