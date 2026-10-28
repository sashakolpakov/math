import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneHalfFillings
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductEquator
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives

/-! # Half -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half

noncomputable section

section

/-! The actual oriented axis interval whose product is the common half-disk boundary. -/

open _root_.CategoryTheory
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def realAxisRayMap (η : Fin 1 → Bool) : C(Convexity.StdSimplex ℝ (Fin 2), ℝ) :=
  ⟨fun t => t.weights 1 * (OrthantSphereEquator.orthantSign (η 0) : ℝ),
    (Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 2)).mul continuous_const⟩

def realAxisRaySimplex (η : Fin 1 → Bool) : (TopCat.toSSet.obj (TopCat.of ℝ)) _⦋1⦌ :=
  ((TopCat.of ℝ).toSSetObjEquiv _).symm (realAxisRayMap η)

theorem realAxisRaySimplex_face_zero (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of ℝ)).δ 0 (realAxisRaySimplex η) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of ℝ)).symm (OrthantSphereEquator.orthantSign (η 0) : ℝ) := by
  apply ((TopCat.of ℝ).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights 1 * (OrthantSphereEquator.orthantSign (η 0) : ℝ) = _
  have h := OrthantSphereEquator.standardSimplexFace_succAbove (0 : Fin 2) t (0 : Fin 1)
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights 1 = t.weights 0 at h
  rw [h, PlaneHalfFaces.oneVertexSimplex_coordinate, one_mul]
  rfl

theorem realAxisRaySimplex_face_one (η : Fin 1 → Bool) :
    (TopCat.toSSet.obj (TopCat.of ℝ)).δ 1 (realAxisRaySimplex η) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of ℝ)).symm 0 := by
  apply ((TopCat.of ℝ).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 1 t).weights 1 * (OrthantSphereEquator.orthantSign (η 0) : ℝ) = 0
  rw [OrthantSphereEquator.standardSimplexFace_omitted_zero, zero_mul]

def realAxisIntervalChain : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of ℝ)).X 1 :=
  ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of ℝ)) (realAxisRaySimplex η)

def realAxisEndpointChain : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of ℝ)).X 0 :=
  ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of ℝ))
    ((TopCat.toSSetObj₀Equiv (X := TopCat.of ℝ)).symm (OrthantSphereEquator.orthantSign (η 0) : ℝ))

theorem realAxisIntervalChain_boundary :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of ℝ)).d 1 0 realAxisIntervalChain = realAxisEndpointChain := by
  have hs : ∀ η (i : Fin 1), (TopCat.toSSet.obj (TopCat.of ℝ)).δ i.succ
      (realAxisRaySimplex (OrthantSphereEquator.orthantFlip i η)) = (TopCat.toSSet.obj (TopCat.of ℝ)).δ i.succ
        (realAxisRaySimplex η) := by
    intro η i
    have hi : i = 0 := by omega
    subst i
    exact (realAxisRaySimplex_face_one _).trans (realAxisRaySimplex_face_one η).symm
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj (TopCat.of ℝ))).d 1 0
    (∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
      (TopCat.toSSet.obj (TopCat.of ℝ)) (realAxisRaySimplex η)) = _
  rw [OrthantWeightedBoundary.orthantWeighted_boundary_first _ 0 _ hs]
  simp only [realAxisRaySimplex_face_zero]
  rfl

def axisPlaneHalfInclusion (b : Bool) : TopCat.of ℝ ⟶ TopCat.of (PlaneHalf.coordinatePlaneHalf b) :=
  TopCat.ofHom ⟨fun s => ⟨ProductEquator.planeAxisVectorOfReal s, by
      change 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * 0
      simp⟩, by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop⟩

theorem realAxisIntervalChain_half_inclusion (b : Bool) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (axisPlaneHalfInclusion b)).f 1 realAxisIntervalChain =
      PlaneHalfFillings.planeHalfAxisChain b := by
  rw [realAxisIntervalChain, PlaneHalfFillings.planeHalfAxisChain, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, OrthantBoundaryRepresentatives.integralSimplexChain_map]
  congr 2
  apply ((TopCat.of (PlaneHalf.coordinatePlaneHalf b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change ProductEquator.planeAxisVectorOfReal (t.weights 1 * (OrthantSphereEquator.orthantSign (η 0) : ℝ)) = t.weights 1 • PlaneHalf.planeAxisVector η
  ext i
  fin_cases i <;> simp [ProductEquator.planeAxisVectorOfReal, PlaneHalf.planeAxisVector]

end

/-!
# ChernClass: the two actual half-intervals for the second sphere boundary

Each signed ray lies in its real half-line. Its product with a
punctured tangent space radially maps into the corresponding sphere
pole chart, using the original ordered axis-product coordinates.
-/

open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def axisHalfLine (b : Bool) : Set ℝ := {s | 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * s}

def axisHalfRayMap (b : Bool) : C(Convexity.StdSimplex ℝ (Fin 2), axisHalfLine b) :=
  ⟨fun t => ⟨t.weights 1 * (OrthantSphereEquator.orthantSign b : ℝ), by
      change 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) * (t.weights 1 * (OrthantSphereEquator.orthantSign b : ℝ))
      cases b <;> norm_num [OrthantSphereEquator.orthantSign]⟩,
    ((Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 2)).mul continuous_const).subtype_mk _⟩

def axisHalfEndpoint (b : Bool) : axisHalfLine b :=
  ⟨(OrthantSphereEquator.orthantSign b : ℝ), by cases b <;> norm_num [axisHalfLine, OrthantSphereEquator.orthantSign]⟩

def axisHalfOrigin (b : Bool) : axisHalfLine b := ⟨0, by simp [axisHalfLine]⟩

def axisHalfRaySimplex (b : Bool) : (TopCat.toSSet.obj (TopCat.of (axisHalfLine b))) _⦋1⦌ :=
  ((TopCat.of (axisHalfLine b)).toSSetObjEquiv _).symm (axisHalfRayMap b)

def axisProductPole (m : ℕ) (b : Bool) : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m :=
  if b then -CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole m else CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole m

theorem axisProduct_radial_mem_chart (m : ℕ) (b : Bool) (s : axisHalfLine b)
    (y : EuclideanSpace ℝ (Fin m)) (h : ProductEquator.axisProductCoordinates m (s.val, y) ≠ 0) :
    CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 1)))
      ⟨ProductEquator.axisProductCoordinates m (s.val, y), h⟩ ∈ CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (axisProductPole m b) := by
  have hcoord : (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 1)))
      ⟨ProductEquator.axisProductCoordinates m (s.val, y), h⟩).val 0 =
      ‖ProductEquator.axisProductCoordinates m (s.val, y)‖⁻¹ * s.val := by
    rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe]
    rfl
  have hsign : 0 ≤ (OrthantSphereEquator.orthantSign b : ℝ) *
      (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 1)))
        ⟨ProductEquator.axisProductCoordinates m (s.val, y), h⟩).val 0 := by
    rw [hcoord, mul_left_comm]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) s.property
  intro he
  have hp := congrArg (fun z : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m => z.val 0) he
  rw [hp] at hsign
  cases b <;> norm_num [axisProductPole, OrthantSphereEquator.orthantSign, CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at hsign

abbrev PuncturedAxisHalf (b : Bool) := {s : axisHalfLine b // s.val ≠ 0}

def axisHalfRightPuncturedMap (m : ℕ) (b : Bool) :
    C(axisHalfLine b × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)),
      CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (m + 1)))) :=
  ⟨fun p => ⟨ProductEquator.axisProductCoordinates m (p.1.val, p.2.val), by
      intro h
      have hz : (p.1.val, p.2.val) = 0 :=
        (ProductEquator.axisProductCoordinates m).injective (h.trans (map_zero _).symm)
      exact p.2.property (congrArg Prod.snd hz)⟩,
    ((ProductEquator.axisProductCoordinates m).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

def axisHalfLeftPuncturedMap (m : ℕ) (b : Bool) :
    C(PuncturedAxisHalf b × EuclideanSpace ℝ (Fin m),
      CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (m + 1)))) :=
  ⟨fun p => ⟨ProductEquator.axisProductCoordinates m (p.1.val.val, p.2), by
      intro h
      have hz : (p.1.val.val, p.2) = 0 :=
        (ProductEquator.axisProductCoordinates m).injective (h.trans (map_zero _).symm)
      exact p.1.property (congrArg Prod.fst hz)⟩,
    ((ProductEquator.axisProductCoordinates m).continuous.comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)).subtype_mk _⟩

def axisHalfRightChartMap (m : ℕ) (b : Bool) :
    C(axisHalfLine b × CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)), CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (axisProductPole m b)) :=
  ⟨fun p => ⟨CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _ (axisHalfRightPuncturedMap m b p),
      axisProduct_radial_mem_chart m b p.1 p.2.val (axisHalfRightPuncturedMap m b p).property⟩,
    ((CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _).continuous.comp (axisHalfRightPuncturedMap m b).continuous).subtype_mk _⟩

def axisHalfLeftChartMap (m : ℕ) (b : Bool) :
    C(PuncturedAxisHalf b × EuclideanSpace ℝ (Fin m), CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (axisProductPole m b)) :=
  ⟨fun p => ⟨CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _ (axisHalfLeftPuncturedMap m b p),
      axisProduct_radial_mem_chart m b p.1.val p.2 (axisHalfLeftPuncturedMap m b p).property⟩,
    ((CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection _).continuous.comp (axisHalfLeftPuncturedMap m b).continuous).subtype_mk _⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half
