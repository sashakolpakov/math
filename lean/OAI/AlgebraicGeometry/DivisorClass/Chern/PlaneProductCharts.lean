import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalf
import OAI.Geometry.Foundations.ConvexStdSimplexMetric

/-! # Plane Product Charts -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCharts

noncomputable section

section

/-!
# ChernClass: ordered coordinates and pole-chart supports for a plane product

The first two coordinates are the coordinate plane; the remaining
coordinates retain their original order. Radial projection carries
each signed half-plane into the corresponding sphere pole chart.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def planeProductLinearEquiv (m : ℕ) :
    (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 2)) where
  toFun x := WithLp.toLp 2 (Fin.cons (x.1 0) (Fin.cons (x.1 1) (fun i => x.2 i)))
  invFun x := (WithLp.toLp 2 (Fin.cons (x 0) (fun _ : Fin 1 => x 1)),
    WithLp.toLp 2 (fun i => x i.succ.succ))
  left_inv x := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · ext i
      rfl
  right_inv x := by
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  map_add' x y := by
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  map_smul' a x := by
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j

def planeProductCoordinates (m : ℕ) :
    (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 2)) :=
  (planeProductLinearEquiv m).toContinuousLinearEquiv

theorem planeProductCoordinates_first (m : ℕ) (x : PlaneHalf.CoordinatePlane) (y : EuclideanSpace ℝ (Fin m)) :
    planeProductCoordinates m (x, y) 0 = x 0 := rfl

theorem planeProductCoordinates_second (m : ℕ) (x : PlaneHalf.CoordinatePlane) (y : EuclideanSpace ℝ (Fin m)) :
    planeProductCoordinates m (x, y) 1 = x 1 := rfl

theorem planeProductCoordinates_tail (m : ℕ) (x : PlaneHalf.CoordinatePlane) (y : EuclideanSpace ℝ (Fin m))
    (i : Fin m) : planeProductCoordinates m (x, y) i.succ.succ = y i := rfl

def planeProductPole (m : ℕ) (b : Bool) : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1) :=
  if b then -CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1) else CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)

theorem planeProduct_radial_mem_chart (m : ℕ) (b : Bool) (x : PlaneHalf.coordinatePlaneHalf b)
    (y : EuclideanSpace ℝ (Fin m)) (hne : planeProductCoordinates m (x.val, y) ≠ 0) :
    CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 2)))
        ⟨planeProductCoordinates m (x.val, y), hne⟩ ∈ CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (planeProductPole m b) := by
  have hcoord :
      (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 2)))
        ⟨planeProductCoordinates m (x.val, y), hne⟩).val 0 =
      ‖planeProductCoordinates m (x.val, y)‖⁻¹ * x.val 0 := by
    rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe]
    rfl
  have hsign : 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) *
      (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 2)))
        ⟨planeProductCoordinates m (x.val, y), hne⟩).val 0 := by
    rw [hcoord, mul_left_comm]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) x.property
  intro h
  have hp := congrArg (fun z : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1) => z.val 0) h
  rw [hp] at hsign
  cases b <;> norm_num [planeProductPole, OrthantSphereEquator.orthantSign, CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at hsign

end

/-!
# ChernClass: actual product maps into the sphere pole charts

A half-disk crossed with a punctured tangent space, and a punctured
half-plane crossed with the full tangent space, both avoid the origin.
Their radial maps land in the required pole chart. These are genuine
continuous maps for applying cross-product naturality.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev PuncturedPlaneHalf (b : Bool) := {x : PlaneHalf.coordinatePlaneHalf b // x.val ≠ 0}

def planeHalfRightPuncturedMap (m : ℕ) (b : Bool) :
    C(PlaneHalf.coordinatePlaneHalf b × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)),
      CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (m + 2)))) :=
  ⟨fun p => ⟨planeProductCoordinates m (p.1.val, p.2.val), by
      intro h
      have hz : (p.1.val, p.2.val) = 0 :=
        (planeProductCoordinates m).injective (h.trans (map_zero _).symm)
      exact p.2.property (congrArg Prod.snd hz)⟩,
    ((planeProductCoordinates m).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

def planeHalfLeftPuncturedMap (m : ℕ) (b : Bool) :
    C(PuncturedPlaneHalf b × EuclideanSpace ℝ (Fin m),
      CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (m + 2)))) :=
  ⟨fun p => ⟨planeProductCoordinates m (p.1.val.val, p.2), by
      intro h
      have hz : (p.1.val.val, p.2) = 0 :=
        (planeProductCoordinates m).injective (h.trans (map_zero _).symm)
      exact p.1.property (congrArg Prod.fst hz)⟩,
    ((planeProductCoordinates m).continuous.comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)).subtype_mk _⟩

def planeHalfRightChartMap (m : ℕ) (b : Bool) :
    C(PlaneHalf.coordinatePlaneHalf b × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)),
      CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (planeProductPole m b)) :=
  ⟨fun p => ⟨CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _ (planeHalfRightPuncturedMap m b p),
      planeProduct_radial_mem_chart m b p.1 p.2.val (planeHalfRightPuncturedMap m b p).property⟩,
    ((CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _).continuous.comp (planeHalfRightPuncturedMap m b).continuous).subtype_mk _⟩

def planeHalfLeftChartMap (m : ℕ) (b : Bool) :
    C(PuncturedPlaneHalf b × EuclideanSpace ℝ (Fin m),
      CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (planeProductPole m b)) :=
  ⟨fun p => ⟨CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _ (planeHalfLeftPuncturedMap m b p),
      planeProduct_radial_mem_chart m b p.1.val p.2 (planeHalfLeftPuncturedMap m b p).property⟩,
    ((CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _).continuous.comp (planeHalfLeftPuncturedMap m b).continuous).subtype_mk _⟩

def planeHalfOuterPuncturedMap (b : Bool) (η : Fin 1 → Bool) :
    C(Convexity.StdSimplex ℝ (Fin 2), PuncturedPlaneHalf b) :=
  ⟨fun t => ⟨PlaneHalf.planeHalfOuterMap b η t, by
      change (OrthantSphereEquator.orthantSphereMap 1 (Fin.cons b η) t).val ≠ 0
      intro h
      have hn := norm_eq_of_mem_sphere (OrthantSphereEquator.orthantSphereMap 1 (Fin.cons b η) t)
      rw [h, norm_zero] at hn
      exact zero_ne_one hn⟩,
    (PlaneHalf.planeHalfOuterMap b η).continuous.subtype_mk _⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCharts
