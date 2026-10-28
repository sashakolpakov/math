import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! # Projective Coordinates In -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

/-!
# Standard coordinate charts on projective space

The projective space here is mathlib's quotient of nonzero vectors by nonzero
scalar multiplication. This file constructs its usual coordinate-ratio charts
and proves their algebraic transition formulas. No scheme or analytic comparison
is assumed or claimed.
-/

variable {K ι : Type*} [Field K]

/-- The homogeneous coordinate ratio `x_j / x_i`, with the usual field convention
that division by zero is zero. Its restriction to the `i`-th patch is the standard
affine coordinate expression. -/
def ratio (i j : ι) : Projectivization K (ι → K) → K :=
  Projectivization.lift (fun v => v.val j / v.val i) (by
    intro a b t h
    have ht : t ≠ 0 := by
      intro ht
      apply a.property
      simpa [ht] using h
    change a.val j / a.val i = b.val j / b.val i
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ ht)

@[simp]
theorem ratio_mk (i j : ι) (v : ι → K) (hv : v ≠ 0) :
    ratio i j (Projectivization.mk K v hv) = v j / v i := rfl

/-- The standard projective patch on which the `i`-th homogeneous coordinate
is nonzero, expressed independently of the chosen homogeneous representative. -/
def InPatch (i : ι) (p : Projectivization K (ι → K)) : Prop := ratio i i p = 1

@[simp]
theorem inPatch_mk_iff (i : ι) (v : ι → K) (hv : v ≠ 0) :
    InPatch i (Projectivization.mk K v hv) ↔ v i ≠ 0 := by
  exact div_self_eq_one₀

/-- The standard projective patches cover all projective points. -/
theorem exists_inPatch (p : Projectivization K (ι → K)) : ∃ i, InPatch i p := by
  classical
  induction p using Projectivization.ind with
  | h v hv =>
    have hex : ∃ i, v i ≠ 0 := by
      by_contra hn
      apply hv
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, (inPatch_mk_iff i v hv).mpr hi⟩

/-- The normalized homogeneous coordinates in the `i`-th patch. -/
def coordinates (i : ι) (p : Projectivization K (ι → K)) : ι → K := fun j => ratio i j p

@[simp]
theorem coordinates_mk (i j : ι) (v : ι → K) (hv : v ≠ 0) :
    coordinates i (Projectivization.mk K v hv) j = v j / v i := rfl

@[simp]
theorem coordinates_self (i : ι) (p : Projectivization K (ι → K))
    (hp : InPatch i p) : coordinates i p i = 1 := hp

/-- On the `i`-th patch, a coordinate in the `j`-th chart is the quotient of
the corresponding two `i`-chart coordinates. -/
theorem transition_formula (i j k : ι) (p : Projectivization K (ι → K))
    (hp : InPatch i p) : ratio j k p = ratio i k p / ratio i j p := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hi : v i ≠ 0 := (inPatch_mk_iff i v hv).mp hp
    exact (div_div_div_cancel_right₀ hi (v k) (v j)).symm

/-- The patch-membership test for a second chart, in the coordinates of the first. -/
theorem inPatch_iff_ratio_ne_zero (i j : ι) (p : Projectivization K (ι → K))
    (hp : InPatch i p) : InPatch j p ↔ ratio i j p ≠ 0 := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hi : v i ≠ 0 := (inPatch_mk_iff i v hv).mp hp
    simp only [inPatch_mk_iff, ratio_mk, ne_eq, div_eq_zero_iff, hi, or_false]

/-- A vector normalized to have coordinate one is nonzero. -/
theorem normalized_ne_zero (i : ι) (v : ι → K) (hv : v i = 1) : v ≠ 0 := by
  intro h
  exact zero_ne_one ((congr_fun h i).symm.trans hv)

/-- The normalized coordinates reconstruct their projective point. -/
theorem mk_coordinates (i : ι) (p : Projectivization K (ι → K))
    (hp : InPatch i p) :
    Projectivization.mk K (coordinates i p) (normalized_ne_zero i _ hp) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    apply (Projectivization.mk_eq_mk_iff' K _ v _ hv).mpr
    refine ⟨(v i)⁻¹, ?_⟩
    funext j
    simp [coordinates, div_eq_mul_inv, mul_comm]

/-- The usual projective coordinate chart, with its affine target represented
as the hyperplane of vectors whose `i`-th coordinate equals one. -/
def normalizedChart (i : ι) :
    {p : Projectivization K (ι → K) // InPatch i p} ≃ {v : ι → K // v i = 1} where
  toFun p := ⟨coordinates i p.val, p.property⟩
  invFun v := ⟨Projectivization.mk K v.val (normalized_ne_zero i v.val v.property), by
    apply (inPatch_mk_iff i _ _).mpr
    rw [v.property]
    exact one_ne_zero⟩
  left_inv p := by
    apply Subtype.ext
    exact mk_coordinates i p.val p.property
  right_inv v := by
    apply Subtype.ext
    funext j
    change v.val j / v.val i = v.val j
    rw [v.property, div_one]

/-- Dropping the normalized coordinate identifies the affine hyperplane with
an ordinary coordinate space indexed by all indices other than `i`. -/
noncomputable def dropNormalizedCoordinate (i : ι) :
    {v : ι → K // v i = 1} ≃ ({j : ι // j ≠ i} → K) := by
  classical
  refine
    { toFun := fun v j => v.val j.val
      invFun := fun f => ⟨fun j => if h : j = i then 1 else f ⟨j, h⟩, by simp⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j
      simp [v.property]
    · simp [h]
  · intro f
    funext j
    simp [j.property]

/-- The standard affine chart of projective space. For `ι = Fin (n+1)`, its
target has exactly `n` coordinate positions. -/
noncomputable def affineChart (i : ι) :
    {p : Projectivization K (ι → K) // InPatch i p} ≃ ({j : ι // j ≠ i} → K) :=
  (normalizedChart i).trans (dropNormalizedCoordinate i)

@[simp]
theorem affineChart_apply (i : ι) (p : {p : Projectivization K (ι → K) // InPatch i p})
    (j : {j : ι // j ≠ i}) : affineChart i p j = ratio i j.val p.val := rfl

/-- The coordinate transition formula specialized to the actual affine-chart
equivalences on a chart overlap. -/
theorem affineChart_transition (i j : ι) (p : Projectivization K (ι → K))
    (hi : InPatch i p) (hj : InPatch j p) (k : {k : ι // k ≠ j}) :
    affineChart j ⟨p, hj⟩ k = ratio i k.val p / ratio i j p :=
  transition_formula i j k.val p hi

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
