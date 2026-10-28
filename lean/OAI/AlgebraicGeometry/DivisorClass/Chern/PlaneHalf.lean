import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator
import OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings

/-! # Plane Half -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalf

noncomputable section

/-!
# ChernClass: geometric half-disks for the complex coordinate plane

Each closed coordinate half-plane is convex and contractible. The actual
oriented circle orthants and the two straight axis rays are singular
simplices in these half-planes. These supports will keep the product
boundary pieces in their prescribed sphere pole charts.
-/

open OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev CoordinatePlane := EuclideanSpace ℝ (Fin 2)

def coordinatePlaneHalf (b : Bool) : Set CoordinatePlane :=
  {x | 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * x 0}

theorem coordinatePlaneHalf_convex (b : Bool) : Convex ℝ (coordinatePlaneHalf b) := by
  intro x hx y hy a c ha hc _
  change 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * (a * x 0 + c * y 0)
  change 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * x 0 at hx
  change 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * y 0 at hy
  calc
    (OrthantSphereEquator.orthantSign b : ℝ) * (a * x 0 + c * y 0) =
        a * ((OrthantSphereEquator.orthantSign b : ℝ) * x 0) + c * ((OrthantSphereEquator.orthantSign b : ℝ) * y 0) := by ring
    _ ≥ 0 := add_nonneg (mul_nonneg ha hx) (mul_nonneg hc hy)

instance coordinatePlaneHalf_contractible (b : Bool) : ContractibleSpace (coordinatePlaneHalf b) :=
  (coordinatePlaneHalf_convex b).contractibleSpace ⟨0, by simp [coordinatePlaneHalf]⟩

theorem orthantSphereMap_signed_coordinate_nonneg (n : ℕ) (ε : Fin (n + 1) → Bool)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    0 ≤ (OrthantSphereEquator.orthantSign (ε i) : ℝ) * (OrthantSphereEquator.orthantSphereMap n ε t).val i := by
  rw [OrthantSphereEquator.orthantSphereMap_coordinate]
  have hn := inv_nonneg.mpr (norm_nonneg (OrthantSphereEquator.orthantVector n ε t))
  have ht := Convexity.StdSimplex.weights_nonneg (w := t) i
  cases ε i <;> norm_num [OrthantSphereEquator.orthantSign] <;> exact mul_nonneg hn ht

def planeHalfOuterMap (b : Bool) (η : Fin 1 → Bool) :
    C(Convexity.StdSimplex ℝ (Fin 2), coordinatePlaneHalf b) :=
  ⟨fun t => ⟨(OrthantSphereEquator.orthantSphereMap 1 (Fin.cons b η) t).val,
      orthantSphereMap_signed_coordinate_nonneg 1 (Fin.cons b η) t 0⟩,
    (continuous_subtype_val.comp (OrthantSphereEquator.orthantSphereMap 1 (Fin.cons b η)).continuous).subtype_mk _⟩

def planeHalfOuterSimplex (b : Bool) (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of (coordinatePlaneHalf b))) _⦋1⦌ :=
  ((TopCat.of (coordinatePlaneHalf b)).toSSetObjEquiv _).symm (planeHalfOuterMap b η)

def planeAxisVector (η : Fin 1 → Bool) : CoordinatePlane :=
  WithLp.toLp 2 (Fin.cons (α := fun _ : Fin 2 => ℝ) 0 (fun _ => (OrthantSphereEquator.orthantSign (η 0) : ℝ)))

def planeAxisRayMap (b : Bool) (η : Fin 1 → Bool) :
    C(Convexity.StdSimplex ℝ (Fin 2), coordinatePlaneHalf b) :=
  ⟨fun t => ⟨t.weights 1 • planeAxisVector η, by
      change 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * (t.weights 1 * 0)
      simp⟩,
    ((Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 2)).smul continuous_const).subtype_mk _⟩

def planeAxisRaySimplex (b : Bool) (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of (coordinatePlaneHalf b))) _⦋1⦌ :=
  ((TopCat.of (coordinatePlaneHalf b)).toSSetObjEquiv _).symm (planeAxisRayMap b η)

def planeAxisPoint (b : Bool) (η : Fin 1 → Bool) : coordinatePlaneHalf b :=
  ⟨planeAxisVector η, by change 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * 0; simp⟩

def planeHalfOrigin (b : Bool) : coordinatePlaneHalf b :=
  ⟨0, by simp [coordinatePlaneHalf]⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalf
