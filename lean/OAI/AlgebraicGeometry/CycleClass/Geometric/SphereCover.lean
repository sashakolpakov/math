import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! # Sphere Cover -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover.Cycles

noncomputable section

/-!
# Two stereographic open sets on a sphere

The complements of opposite poles form an actual open cover of the unit sphere.
Each complement is homeomorphic to a real vector space and hence contractible.
Their intersection is homeomorphic to a punctured hyperplane and is therefore
homotopy equivalent to a sphere in one lower ambient dimension.

No excision, Mayer--Vietoris theorem, or sphere-homology computation is assumed.
-/

open _root_.Metric _root_.Module _root_.Submodule
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- The stereographic domain obtained by deleting a pole from the sphere. -/
def spherePoleOpen (v : NormalSphere.Cycles.NormalUnitSphere E) : Set (NormalSphere.Cycles.NormalUnitSphere E) := {v}ᶜ

@[simp]
theorem mem_spherePoleOpen (v x : NormalSphere.Cycles.NormalUnitSphere E) :
    x ∈ spherePoleOpen v ↔ x ≠ v := Iff.rfl

theorem isOpen_spherePoleOpen (v : NormalSphere.Cycles.NormalUnitSphere E) : IsOpen (spherePoleOpen v) :=
  isOpen_compl_singleton

variable [InnerProductSpace ℝ E]

/-- Opposite poles have disjoint omitted singleton sets. -/
theorem spherePoleOpen_union (v : NormalSphere.Cycles.NormalUnitSphere E) :
    spherePoleOpen v ∪ spherePoleOpen (-v) = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_spherePoleOpen, Set.mem_univ, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ ne_neg_of_mem_unit_sphere ℝ v)
  · exact Or.inl h

/-- The hyperplane perpendicular to the chosen pole. -/
abbrev SphereEquatorSpace (v : NormalSphere.Cycles.NormalUnitSphere E) := (ℝ ∙ (v : E))ᗮ

/-- The actual stereographic homeomorphism on a pole complement. -/
def spherePoleChart (v : NormalSphere.Cycles.NormalUnitSphere E) :
    spherePoleOpen v ≃ₜ SphereEquatorSpace v :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

@[simp]
theorem spherePoleChart_apply (v : NormalSphere.Cycles.NormalUnitSphere E) (x : spherePoleOpen v) :
    spherePoleChart v x = stereographic (norm_eq_of_mem_sphere v) (x : NormalSphere.Cycles.NormalUnitSphere E) :=
  rfl

/-- Every pole complement is genuinely contractible. -/
theorem spherePoleOpen_contractible (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ContractibleSpace (spherePoleOpen v) :=
  (spherePoleChart v).contractibleSpace

/-- The opposite pole, viewed as a point of the chosen stereographic chart. -/
def sphereOppositePole (v : NormalSphere.Cycles.NormalUnitSphere E) : spherePoleOpen v :=
  ⟨-v, (ne_neg_of_mem_unit_sphere ℝ v).symm⟩

@[simp]
theorem spherePoleChart_opposite (v : NormalSphere.Cycles.NormalUnitSphere E) :
    spherePoleChart v (sphereOppositePole v) = 0 := by
  exact stereographic_apply_neg v

/-- Deleting the opposite pole from this chart is exactly deleting zero from
the hyperplane. -/
theorem spherePoleChart_eq_zero_iff (v : NormalSphere.Cycles.NormalUnitSphere E) (x : spherePoleOpen v) :
    spherePoleChart v x = 0 ↔ (x : NormalSphere.Cycles.NormalUnitSphere E) = -v := by
  constructor
  · intro h
    have he : spherePoleChart v x = spherePoleChart v (sphereOppositePole v) := by
      rw [h, spherePoleChart_opposite]
    exact congrArg Subtype.val ((spherePoleChart v).injective he)
  · intro h
    have he : x = sphereOppositePole v := Subtype.ext h
    rw [he, spherePoleChart_opposite]

/-- Flatten the two membership conditions in the intersection of the charts. -/
def spherePoleIntersectionNested (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ↥(spherePoleOpen v ∩ spherePoleOpen (-v)) ≃ₜ
      {x : spherePoleOpen v // (x : NormalSphere.Cycles.NormalUnitSphere E) ≠ -v} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The overlap of the two stereographic domains is a punctured real
hyperplane, via the restricted stereographic homeomorphism. -/
def spherePoleIntersectionChart (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ↥(spherePoleOpen v ∩ spherePoleOpen (-v)) ≃ₜ NormalSphere.Cycles.PuncturedNormal (SphereEquatorSpace v) :=
  (spherePoleIntersectionNested v).trans
    ((spherePoleChart v).subtype (fun x => by
      change (x : NormalSphere.Cycles.NormalUnitSphere E) ≠ -v ↔ spherePoleChart v x ≠ 0
      exact (not_congr (spherePoleChart_eq_zero_iff v x)).symm))

@[simp]
theorem spherePoleIntersectionChart_apply (v : NormalSphere.Cycles.NormalUnitSphere E)
    (x : ↥(spherePoleOpen v ∩ spherePoleOpen (-v))) :
    (spherePoleIntersectionChart v x : SphereEquatorSpace v) =
      stereographic (norm_eq_of_mem_sphere v) (x : NormalSphere.Cycles.NormalUnitSphere E) := rfl

/-- Radial normalization in stereographic coordinates identifies the overlap
up to homotopy with the unit sphere of the equatorial hyperplane. -/
def spherePoleIntersectionSphereEquiv (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ContinuousMap.HomotopyEquiv ↥(spherePoleOpen v ∩ spherePoleOpen (-v))
      (NormalSphere.Cycles.NormalUnitSphere (SphereEquatorSpace v)) :=
  (spherePoleIntersectionChart v).toHomotopyEquiv.trans
    (NormalSphere.Cycles.normalSphereHomotopyEquiv (SphereEquatorSpace v))

/-- The equatorial hyperplane has one less real dimension. -/
theorem sphereEquatorSpace_finrank [FiniteDimensional ℝ E] (v : NormalSphere.Cycles.NormalUnitSphere E) :
    Module.finrank ℝ (SphereEquatorSpace v) + 1 = Module.finrank ℝ E := by
  have h := (ℝ ∙ (v : E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton (ne_zero_of_mem_unit_sphere v)] at h
  simpa [Nat.add_comm] using h

/-- In an `(n+1)`-dimensional inner product space, the equatorial sphere is
homeomorphic to the usual unit sphere in real Euclidean `n`-space. -/
def sphereEquatorEuclideanHomeomorph (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (v : NormalSphere.Cycles.NormalUnitSphere E) :
    NormalSphere.Cycles.NormalUnitSphere (SphereEquatorSpace v) ≃ₜ
      NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n)) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.subtype
    (fun x => by
      simp only [NormalSphere.Cycles.NormalUnitSphere, mem_sphere_zero_iff_norm]
      change ‖x‖ = 1 ↔
        ‖(OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr x‖ = 1
      rw [LinearIsometryEquiv.norm_map])

/-- The explicit lower-dimensional sphere equivalence used in dimension
induction for the two-chart cover. -/
def spherePoleIntersectionLowerSphereEquiv (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ContinuousMap.HomotopyEquiv ↥(spherePoleOpen v ∩ spherePoleOpen (-v))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n))) :=
  (spherePoleIntersectionSphereEquiv v).trans
    (sphereEquatorEuclideanHomeomorph n v).toHomotopyEquiv

/-- A concrete north pole for the standard sphere. -/
def standardSphereNorthPole (n : ℕ) : NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨EuclideanSpace.single 0 1, by simp [NormalSphere.Cycles.NormalUnitSphere]⟩

section OrderedEquatorCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev StandardEquator (n : ℕ) := SphereEquatorSpace (standardSphereNorthPole n)

theorem standardEquator_first_zero (n : ℕ) (x : StandardEquator n) : x.val 0 = 0 := by
  have h := x.property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at h
  simpa [standardSphereNorthPole, EuclideanSpace.inner_single_right] using h

def orderedEquatorCoordinates (n : ℕ) : StandardEquator n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x.val i.succ)
  invFun y := ⟨WithLp.toLp 2 (Fin.cons 0 (fun i => y i)), by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [standardSphereNorthPole, EuclideanSpace.inner_single_right]⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (standardEquator_first_zero n x).symm
    · rfl
  right_inv y := by ext i; rfl
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (fun i : Fin n => x.val i.succ)‖ ^ 2 = ‖x.val‖ ^ 2
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp only [standardEquator_first_zero, zero_pow (by decide : 2 ≠ 0), zero_add]

def orderedEquatorBasis (n : ℕ) : OrthonormalBasis (Fin n) ℝ (StandardEquator n) :=
  OrthonormalBasis.ofRepr (orderedEquatorCoordinates n)

theorem orderedEquatorCoordinates_apply (n : ℕ) (x : StandardEquator n) (i : Fin n) :
    orderedEquatorCoordinates n x i = x.val i.succ := rfl

def orderedEquatorSphereHomeomorph (n : ℕ) :
    NormalSphere.Cycles.NormalUnitSphere (StandardEquator n) ≃ₜ NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n)) :=
  (orderedEquatorCoordinates n).toHomeomorph.subtype (fun x => by
    simp only [NormalSphere.Cycles.NormalUnitSphere, mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖orderedEquatorCoordinates n x‖ = 1
    rw [LinearIsometryEquiv.norm_map])

end OrderedEquatorCoordinates

/-- The two-chart intersection for the standard `n`-sphere has the homotopy
type of the unit sphere in real `n`-space. This also handles `n = 0`, when
both the intersection and that lower sphere are empty. -/
def standardSphereOverlapEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(spherePoleOpen (standardSphereNorthPole n) ∩
        spherePoleOpen (-standardSphereNorthPole n))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n))) :=
  (spherePoleIntersectionSphereEquiv (standardSphereNorthPole n)).trans
    (orderedEquatorSphereHomeomorph n).toHomotopyEquiv

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover.Cycles
