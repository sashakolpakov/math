import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover
import OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction
import OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.AlgebraicTopology.SingularSet
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

/-! # Orthant Sphere Equator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator

noncomputable section

section

/-!
# ChernClass: explicit oriented orthants on the standard sphere

Each signed coordinate facet is a genuine singular simplex: interpolate its
signed coordinate vertices and normalize radially. Its barycentric coordinates
cannot all vanish. These maps supply concrete sphere chains for comparing
the ordered sphere normalization with products of complex orientations.
-/

open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def orthantSign (b : Bool) : ℤ := if b then 1 else -1

theorem orthantSign_ne_zero (b : Bool) : orthantSign b ≠ 0 := by cases b <;> norm_num [orthantSign]

theorem orthantSign_not (b : Bool) : orthantSign (!b) = -orthantSign b := by
  cases b <;> norm_num [orthantSign]

theorem orthantSign_norm (b : Bool) : ‖(orthantSign b : ℝ)‖ = 1 := by
  cases b <;> norm_num [orthantSign]

def orthantVector (n : ℕ) (ε : Fin (n + 1) → Bool) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨fun t => WithLp.toLp 2 (fun i => (orthantSign (ε i) : ℝ) * t.weights i), by
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun i => continuous_const.mul
      (Convexity.StdSimplex.continuous_weights_apply ℝ i)⟩

theorem orthantVector_ne_zero (n : ℕ) (ε : Fin (n + 1) → Bool)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) : orthantVector n ε t ≠ 0 := by
  intro h
  have ht : ∀ i, t.weights i = 0 := by
    intro i
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x i) h
    change (orthantSign (ε i) : ℝ) * t.weights i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast orthantSign_ne_zero (ε i))
  have hs := Convexity.StdSimplex.total_of_fintype t
  change (∑ i, t.weights i) = 1 at hs
  simp only [ht, Finset.sum_const_zero] at hs
  exact zero_ne_one hs

def orthantPuncturedSimplex (n : ℕ) (ε : Fin (n + 1) → Bool) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (n + 1)))) :=
  ⟨fun t => ⟨orthantVector n ε t, orthantVector_ne_zero n ε t⟩,
    (orthantVector n ε).continuous.subtype_mk (orthantVector_ne_zero n ε)⟩

def orthantSphereMap (n : ℕ) (ε : Fin (n + 1) → Bool) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) :=
  (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (n + 1)))).comp (orthantPuncturedSimplex n ε)

theorem orthantSphereMap_coe (n : ℕ) (ε : Fin (n + 1) → Bool)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (orthantSphereMap n ε t).val = ‖orthantVector n ε t‖⁻¹ • orthantVector n ε t :=
  CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe _ _

def orthantSphereSimplex (n : ℕ) (ε : Fin (n + 1) → Bool) :
    (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)) _⦋n⦌ :=
  ((CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n).toSSetObjEquiv _).symm (orthantSphereMap n ε)

/-- Flipping a sign at a vanishing barycentric coordinate fixes the
actual interpolated vector and hence its radial sphere point. -/
theorem orthantSphereMap_update_zero (n : ℕ) (ε : Fin (n + 1) → Bool)
    (i : Fin (n + 1)) (b : Bool) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (ht : t.weights i = 0) :
    orthantSphereMap n (Function.update ε i b) t = orthantSphereMap n ε t := by
  have hv : orthantVector n (Function.update ε i b) t = orthantVector n ε t := by
    ext j
    change (orthantSign (Function.update ε i b j) : ℝ) * t.weights j =
      (orthantSign (ε j) : ℝ) * t.weights j
    by_cases hj : j = i
    · subst j
      simp only [ht, mul_zero]
    · rw [Function.update_of_ne hj]
  apply Subtype.ext
  rw [orthantSphereMap_coe, orthantSphereMap_coe, hv]

end

section

/-! Pair actual orthant faces across the coordinate hyperplane they share. -/

open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem standardSimplexFace_omitted_zero {n : ℕ} (i : Fin (n + 2))
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) : (OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i t).weights i = 0 := by
  change (Convexity.StdSimplex.map i.succAbove t).weights i = 0
  rw [Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_of_notMem_range t.weights i (by simp)

theorem orthantSphereSimplex_face_update {n : ℕ} (ε : Fin (n + 2) → Bool)
    (i : Fin (n + 2)) (b : Bool) :
    (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).δ i
        (orthantSphereSimplex (n + 1) (Function.update ε i b)) =
      (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).δ i (orthantSphereSimplex (n + 1) ε) := by
  apply ((CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  exact orthantSphereMap_update_zero (n + 1) ε i b (OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i t)
    (standardSimplexFace_omitted_zero i t)

def orthantFlip {m : ℕ} (i : Fin m) (ε : Fin m → Bool) : Fin m → Bool :=
  Function.update ε i (!(ε i))

theorem orthantFlip_involutive {m : ℕ} (i : Fin m) : Function.Involutive (orthantFlip i) := by
  intro ε
  funext j
  by_cases h : j = i
  · subst j
    simp [orthantFlip]
  · simp [orthantFlip, Function.update_of_ne h]

theorem orthantFlip_ne {m : ℕ} (i : Fin m) (ε : Fin m → Bool) : orthantFlip i ε ≠ ε := by
  intro h
  have hi := congrFun h i
  change Function.update ε i (!(ε i)) i = ε i at hi
  rw [Function.update_self] at hi
  cases hε : ε i <;> simp [hε] at hi

def orthantWeight {m : ℕ} (ε : Fin m → Bool) : ℤ := ∏ i, orthantSign (ε i)

theorem orthantWeight_flip {m : ℕ} (i : Fin m) (ε : Fin m → Bool) :
    orthantWeight (orthantFlip i ε) = -orthantWeight ε := by
  classical
  have hprod (η : Fin m → Bool) : orthantWeight η =
      orthantSign (η i) * ∏ j ∈ Finset.univ.erase i, orthantSign (η j) := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hprod, hprod]
  have hi : orthantSign (orthantFlip i ε i) = -orthantSign (ε i) := by
    rw [orthantFlip, Function.update_self, orthantSign_not]
  have hr : (∏ j ∈ Finset.univ.erase i, orthantSign (orthantFlip i ε j)) =
      ∏ j ∈ Finset.univ.erase i, orthantSign (ε j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [orthantFlip, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hi, hr, neg_mul]

end

section

/-! The actual orthant simplices lie in their prescribed sphere pole charts. -/

open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem orthantSphereMap_coordinate (n : ℕ) (ε : Fin (n + 1) → Bool)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (orthantSphereMap n ε t).val i =
      ‖orthantVector n ε t‖⁻¹ * ((orthantSign (ε i) : ℝ) * t.weights i) := by
  rw [orthantSphereMap_coe]
  rfl

theorem orthantSphereMap_firstChart {n : ℕ} (ε : Fin (n + 1) → Bool) (hε : ε 0 = false)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    orthantSphereMap n ε t ∈ CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole n) := by
  have hle : (orthantSphereMap n ε t).val 0 ≤ 0 := by
    rw [orthantSphereMap_coordinate, hε]
    rw [show (orthantSign false : ℝ) = -1 by norm_num [orthantSign]]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Convexity.StdSimplex.weights_nonneg (w := t) 0))
  intro h
  have h0 := congrArg (fun x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n => x.val 0) h
  have hp : (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole n).val 0 = 1 := by simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole]
  rw [h0, hp] at hle
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hle

theorem orthantSphereMap_secondChart {n : ℕ} (ε : Fin (n + 1) → Bool) (hε : ε 0 = true)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    orthantSphereMap n ε t ∈ CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole n) := by
  have hle : 0 ≤ (orthantSphereMap n ε t).val 0 := by
    rw [orthantSphereMap_coordinate, hε]
    rw [show (orthantSign true : ℝ) = 1 by norm_num [orthantSign]]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (mul_nonneg zero_le_one (Convexity.StdSimplex.weights_nonneg (w := t) 0))
  intro h
  have h0 := congrArg (fun x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n => x.val 0) h
  have hp : (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole n).val 0 = -1 := by simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole]
  rw [h0, hp] at hle
  exact (by norm_num : ¬ (0 : ℝ) ≤ -1) hle

def orthantFirstChartMap (n : ℕ) (η : Fin (n + 1) → Bool) :
    C(Convexity.StdSimplex ℝ (Fin (n + 2)), CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) :=
  ⟨fun t => ⟨orthantSphereMap (n + 1) (Fin.cons false η) t,
      orthantSphereMap_firstChart _ rfl t⟩,
    (orthantSphereMap (n + 1) (Fin.cons false η)).continuous.subtype_mk
      (orthantSphereMap_firstChart _ rfl)⟩

def orthantSecondChartMap (n : ℕ) (η : Fin (n + 1) → Bool) :
    C(Convexity.StdSimplex ℝ (Fin (n + 2)), CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) :=
  ⟨fun t => ⟨orthantSphereMap (n + 1) (Fin.cons true η) t,
      orthantSphereMap_secondChart _ rfl t⟩,
    (orthantSphereMap (n + 1) (Fin.cons true η)).continuous.subtype_mk
      (orthantSphereMap_secondChart _ rfl)⟩

theorem orthantWeight_cons (n : ℕ) (b : Bool) (η : Fin n → Bool) :
    orthantWeight (Fin.cons b η) = orthantSign b * orthantWeight η := by
  unfold orthantWeight
  rw [Fin.prod_univ_succ]
  rfl

end

section

/-! The explicit equator inclusion and the actual ordered overlap retraction. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def orderedEquatorVector (n : ℕ) (x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) :
    CycleClass.Geometric.SphereCover.Cycles.StandardEquator (n + 1) :=
  (CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm x.val

theorem orderedEquatorVector_norm (n : ℕ) (x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) : ‖orderedEquatorVector n x‖ = 1 :=
  ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm.norm_map _).trans (norm_eq_of_mem_sphere x)

def orderedEquatorSpherePoint (n : ℕ) (x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1) :=
  ⟨(orderedEquatorVector n x).val, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact orderedEquatorVector_norm n x⟩

theorem orderedEquatorSpherePoint_first_zero (n : ℕ) (x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) :
    (orderedEquatorSpherePoint n x).val 0 = 0 :=
  CycleClass.Geometric.SphereCover.Cycles.standardEquator_first_zero (n + 1) (orderedEquatorVector n x)

theorem orderedEquatorSpherePoint_overlap (n : ℕ) (x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) :
    orderedEquatorSpherePoint n x ∈
      CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) ∩ CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) := by
  constructor
  · intro h
    have he := congrArg (fun z : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1) => z.val 0) h
    rw [orderedEquatorSpherePoint_first_zero] at he
    simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at he
  · intro h
    have he := congrArg (fun z : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1) => z.val 0) h
    rw [orderedEquatorSpherePoint_first_zero] at he
    simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at he

def orderedEquatorOverlap (n : ℕ) : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n ⟶
    TopCat.of ↥(CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) ∩
      CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) :=
  TopCat.ofHom ⟨fun x => ⟨orderedEquatorSpherePoint n x, orderedEquatorSpherePoint_overlap n x⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm.continuous.comp continuous_subtype_val)⟩

theorem orderedEquatorOverlap_stereographic (n : ℕ) (x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) :
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) (orderedEquatorOverlap n x) :
      CycleClass.Geometric.SphereCover.Cycles.StandardEquator (n + 1)) = (2 : ℝ) • orderedEquatorVector n x := by
  rw [CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart_apply, stereographic_apply]
  have hi : inner ℝ (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1) : EuclideanSpace ℝ (Fin (n + 2)))
      (orderedEquatorSpherePoint n x : EuclideanSpace ℝ (Fin (n + 2))) = 0 := by
    simp [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole, EuclideanSpace.inner_single_left, orderedEquatorSpherePoint_first_zero]
  change (2 / (1 - inner ℝ (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1) : EuclideanSpace ℝ (Fin (n + 2)))
      (orderedEquatorSpherePoint n x : EuclideanSpace ℝ (Fin (n + 2))))) •
    (CycleClass.Geometric.SphereCover.Cycles.StandardEquator (n + 1)).orthogonalProjectionOnto
      (orderedEquatorVector n x).val = _
  rw [hi, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  norm_num

theorem orderedEquatorOverlap_radial (n : ℕ) (x : CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) :
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionSphereEquiv (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) (orderedEquatorOverlap n x) :
      CycleClass.Geometric.SphereCover.Cycles.StandardEquator (n + 1)) = orderedEquatorVector n x := by
  change (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (CycleClass.Geometric.SphereCover.Cycles.StandardEquator (n + 1))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionChart (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) (orderedEquatorOverlap n x))).val = _
  rw [CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe, orderedEquatorOverlap_stereographic,
    norm_smul, orderedEquatorVector_norm, smul_smul]
  norm_num

/-- The repaired lower-sphere map restores the original equator point
with exactly its original ordered coordinates. -/
theorem orderedEquatorOverlap_retraction (n : ℕ) :
    orderedEquatorOverlap n ≫ TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (n + 1)).toFun =
      𝟙 (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleIntersectionSphereEquiv (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) (orderedEquatorOverlap n x)) = x.val
  rw [orderedEquatorOverlap_radial]
  exact (CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).apply_symm_apply x.val

end

/-! The uncancelled hemisphere face is exactly the ordered equator simplex. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem standardSimplexFace_succAbove {n : ℕ} (i : Fin (n + 2))
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    (OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i t).weights (i.succAbove j) = t.weights j := by
  change (Convexity.StdSimplex.map i.succAbove t).weights (i.succAbove j) = t.weights j
  rw [Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective t.weights j

theorem orthantVector_face_zero (n : ℕ) (b : Bool) (η : Fin (n + 1) → Bool)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    orthantVector (n + 1) (Fin.cons b η) (OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t) =
      ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm (orthantVector n η t)).val := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · change (orthantSign b : ℝ) * (OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights 0 = 0
    rw [standardSimplexFace_omitted_zero, mul_zero]
  · change (orthantSign (η i) : ℝ) * (OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights i.succ =
      (orthantSign (η i) : ℝ) * t.weights i
    have hi : (0 : Fin (n + 2)).succAbove i = i.succ := rfl
    rw [← hi, standardSimplexFace_succAbove]

theorem orthantSphereMap_face_zero (n : ℕ) (b : Bool) (η : Fin (n + 1) → Bool)
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    orthantSphereMap (n + 1) (Fin.cons b η) (OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t) =
      orderedEquatorSpherePoint n (orthantSphereMap n η t) := by
  apply Subtype.ext
  rw [orthantSphereMap_coe, orthantVector_face_zero]
  change ‖((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm (orthantVector n η t)).val‖⁻¹ •
      ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm (orthantVector n η t)).val =
    ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm (orthantSphereMap n η t).val).val
  rw [orthantSphereMap_coe, map_smul]
  have hn : ‖((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm (orthantVector n η t)).val‖ =
      ‖orthantVector n η t‖ :=
    (CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates (n + 1)).symm.norm_map _
  rw [hn]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator
