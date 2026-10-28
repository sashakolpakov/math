import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator

/-! # Orthant Hemisphere Faces -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantHemisphereFaces

noncomputable section

/-! The internal faces of the two explicit oriented hemispheres cancel. -/

open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem orthantFlip_cons {m : ℕ} (b : Bool) (η : Fin m → Bool) (i : Fin m) :
    Fin.cons b (OrthantSphereEquator.orthantFlip i η) = OrthantSphereEquator.orthantFlip i.succ (Fin.cons b η) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [OrthantSphereEquator.orthantFlip, (Fin.succ_ne_zero i).symm]
  · simp [OrthantSphereEquator.orthantFlip, Function.update_apply]

def orthantFirstChartSimplex (n : ℕ) (η : Fin (n + 1) → Bool) :
    (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))) _⦋n + 1⦌ :=
  ((TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))).toSSetObjEquiv _).symm
    (OrthantSphereEquator.orthantFirstChartMap n η)

def orthantSecondChartSimplex (n : ℕ) (η : Fin (n + 1) → Bool) :
    (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))) _⦋n + 1⦌ :=
  ((TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))).toSSetObjEquiv _).symm
    (OrthantSphereEquator.orthantSecondChartMap n η)

theorem orthantFirstChartSimplex_face_flip (n : ℕ) (η : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).δ i.succ
        (orthantFirstChartSimplex n (OrthantSphereEquator.orthantFlip i η)) =
      (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).δ i.succ
        (orthantFirstChartSimplex n η) := by
  apply ((TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  apply Subtype.ext
  change OrthantSphereEquator.orthantSphereMap (n + 1) (Fin.cons false (OrthantSphereEquator.orthantFlip i η)) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.succ t) =
    OrthantSphereEquator.orthantSphereMap (n + 1) (Fin.cons false η) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.succ t)
  rw [orthantFlip_cons]
  exact OrthantSphereEquator.orthantSphereMap_update_zero (n + 1) (Fin.cons false η) i.succ _ _
    (OrthantSphereEquator.standardSimplexFace_omitted_zero i.succ t)

theorem orthantSecondChartSimplex_face_flip (n : ℕ) (η : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).δ i.succ
        (orthantSecondChartSimplex n (OrthantSphereEquator.orthantFlip i η)) =
      (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).δ i.succ
        (orthantSecondChartSimplex n η) := by
  apply ((TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  apply Subtype.ext
  change OrthantSphereEquator.orthantSphereMap (n + 1) (Fin.cons true (OrthantSphereEquator.orthantFlip i η)) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.succ t) =
    OrthantSphereEquator.orthantSphereMap (n + 1) (Fin.cons true η) (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i.succ t)
  rw [orthantFlip_cons]
  exact OrthantSphereEquator.orthantSphereMap_update_zero (n + 1) (Fin.cons true η) i.succ _ _
    (OrthantSphereEquator.standardSimplexFace_omitted_zero i.succ t)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantHemisphereFaces
