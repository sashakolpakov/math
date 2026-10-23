import StickKnots.CertificationLogic
import StickKnots.Counting
import StickKnots.PolygonalCore

/-!
# End-to-end conditional certificate for the stick-knot upper bound

This module states the two genuinely external inputs at their natural typed
boundaries and checks the entire deduction from them to the knot-count bound.

* The real-algebraic input is applied to the actual degree-four
  `MvPolynomial` family from `PolygonalCore`, not to a free component count.
* The topological input is a classifier on the actual wall-free polygon
  locus, constant on genuine mathlib paths and surjective onto the subtype of
  knot types with stick number at most `N`.

The result is therefore a complete *conditional certificate*: Lean proves the
manuscript logic `external theorems → advertised finite upper bound`, while
the Barone--Basu theorem and ambient-isotopy/support theorem remain explicit
inputs rather than project axioms.
-/

namespace StickKnots

open scoped BigOperators

noncomputable section

/-- The complement of the zero sets of a finite family of real
multivariate polynomials. -/
abbrev PolynomialNonzeroSpace {ι ρ : Type*} (P : ρ → MvPolynomial ι ℝ) :=
  {x : ι → ℝ // ∀ r, MvPolynomial.eval x (P r) ≠ 0}

/-- The actual redundant wall family, viewed in uncurried Euclidean
coordinates. -/
abbrev PolygonWallNonzeroSpace (N : ℕ) :=
  PolynomialNonzeroSpace (Config.indexedWallPolynomial (N := N))

/-- The geometric wall-free locus is homeomorphic to the nonzero locus of the
genuine multivariate wall family. -/
def wallFreePolynomialHomeomorph (N : ℕ) :
    Config.WallFreeSpace N ≃ₜ PolygonWallNonzeroSpace N where
  toFun p := ⟨p.1.coordinateAssignment,
    (Config.wallFree_iff_forall_indexedWallPolynomial_ne_zero p.1).mp p.2⟩
  invFun x :=
    ⟨fun i k ↦ x.1 (i, k),
      (Config.wallFree_iff_forall_indexedWallPolynomial_ne_zero _).mpr x.2⟩
  left_inv p := by
    ext i k
    rfl
  right_inv x := by
    apply Subtype.ext
    funext ⟨i, k⟩
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous fun p : Config.WallFreeSpace N => Function.uncurry p.1
    exact (Homeomorph.piCurry (X := Fin N) (Y := Fin 3) (Z := ℝ)).symm.continuous.comp
      continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous fun x : PolygonWallNonzeroSpace N => Function.curry x.1
    exact (Homeomorph.piCurry (X := Fin N) (Y := Fin 3) (Z := ℝ)).continuous.comp
      continuous_subtype_val

/-- The weighted sum in the fixed-degree component theorem. -/
def algebraicComponentSum (m s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ j * (s + 1).choose j

/-- The conclusion required from the external fixed-degree
real-algebraic component theorem for one concrete polynomial family. -/
structure PolynomialComponentBound {ι ρ : Type*}
    [Fintype ι] [Fintype ρ] (P : ρ → MvPolynomial ι ℝ) (factor : ℕ) where
  finiteComponents : Finite (ConnectedComponents (PolynomialNonzeroSpace P))
  bound :
    (Nat.card (ConnectedComponents (PolynomialNonzeroSpace P)) : ℝ) ≤
      (factor : ℝ) ^ Fintype.card ι *
        algebraicComponentSum (Fintype.card ι) (Fintype.card ρ)

/-- A theorem-shaped Barone--Basu input.  It accepts any finite family of
real polynomials of degree at most four and returns the required component
bound.  No knot-specific conclusion occurs in this interface. -/
def DegreeFourComponentTheorem (factor : ℕ) : Prop :=
  ∀ {ι ρ : Type} [Fintype ι] [Fintype ρ]
    (P : ρ → MvPolynomial ι ℝ),
    (∀ r, (P r).totalDegree ≤ 4) → PolynomialComponentBound P factor

/-- The bounded-stick subtype which the manuscript counts. -/
abbrev BoundedStickKnot {KnotType : Type*} (stickNumber : KnotType → ℕ) (N : ℕ) :=
  {K : KnotType // stickNumber K ≤ N}

/-- Typed topology/support input for the actual wall-free polygon space.
`path_invariant` is precisely where polygonal isotopy and ambient-isotopy
extension enter; `support` is precisely where existence and generic
perturbation of representatives enter. -/
structure StickKnotSemanticInput (N : ℕ) (KnotType : Type*)
    (stickNumber : KnotType → ℕ) where
  certificate : PathClassificationCertificate (Config.WallFreeSpace N)
    (BoundedStickKnot stickNumber N)

private theorem card_coordinateIndex (N : ℕ) :
    Fintype.card (Config.CoordinateIndex N) = 3 * N := by
  simp [Config.CoordinateIndex]
  omega

/-- The Barone--Basu input specialized by Lean to the actual polygon wall
polynomials. -/
theorem polygonPolynomialComponentBound {N factor : ℕ}
    (baroneBasu : DegreeFourComponentTheorem factor) :
    PolynomialComponentBound
      (Config.indexedWallPolynomial (N := N)) factor :=
  baroneBasu (Config.indexedWallPolynomial (N := N))
    Config.totalDegree_indexedWallPolynomial_le

/-- Transport the external component finiteness statement from polynomial
coordinates to the actual path-component type of wall-free polygons. -/
theorem polygonPathComponentBoundFromBaroneBasu {N factor : ℕ}
    (baroneBasu : DegreeFourComponentTheorem factor) :
    PathComponentBound (Config.WallFreeSpace N)
      (Nat.card (ConnectedComponents (PolygonWallNonzeroSpace N))) := by
  let bb := polygonPolynomialComponentBound (N := N) baroneBasu
  let e := wallFreePolynomialHomeomorph N
  let ccEquiv := connectedComponentsEquivOfHomeomorph e
  letI : Finite (ConnectedComponents (PolygonWallNonzeroSpace N)) :=
    bb.finiteComponents
  letI : Finite (ConnectedComponents (Config.WallFreeSpace N)) :=
    Finite.of_injective ccEquiv ccEquiv.injective
  letI : Finite (ZerothHomotopy (Config.WallFreeSpace N)) :=
    Finite.of_injective connectedComponentsEquivZerothHomotopy.symm
      connectedComponentsEquivZerothHomotopy.symm.injective
  refine ⟨inferInstance, ?_⟩
  rw [natCard_pathComponents_eq_connectedComponents]
  exact Nat.le_of_eq (Nat.card_congr ccEquiv)

/-- Complete typed composition of topology/support and real-algebraic
component counting, before simplifying the binomial sum. -/
theorem boundedStickKnot_count_le_algebraicSum
    {N factor : ℕ} {KnotType : Type*} {stickNumber : KnotType → ℕ}
    (semantic : StickKnotSemanticInput N KnotType stickNumber)
    (baroneBasu : DegreeFourComponentTheorem factor) :
    (Nat.card (BoundedStickKnot stickNumber N) : ℝ) ≤
      (factor : ℝ) ^ (3 * N) *
        algebraicComponentSum (3 * N) (N + N * N) := by
  let bb := polygonPolynomialComponentBound (N := N) baroneBasu
  have hcount : Nat.card (BoundedStickKnot stickNumber N) ≤
      Nat.card (ConnectedComponents (PolygonWallNonzeroSpace N)) :=
    class_count_le_of_certificates semantic.certificate
      (polygonPathComponentBoundFromBaroneBasu baroneBasu)
  have hcountR : (Nat.card (BoundedStickKnot stickNumber N) : ℝ) ≤
      Nat.card (ConnectedComponents (PolygonWallNonzeroSpace N)) := by
    exact_mod_cast hcount
  calc
    (Nat.card (BoundedStickKnot stickNumber N) : ℝ) ≤
        Nat.card (ConnectedComponents (PolygonWallNonzeroSpace N)) := hcountR
    _ ≤ (factor : ℝ) ^ Fintype.card (Config.CoordinateIndex N) *
        algebraicComponentSum (Fintype.card (Config.CoordinateIndex N))
          (Fintype.card (Config.WallIndex N)) := bb.bound
    _ = (factor : ℝ) ^ (3 * N) *
        algebraicComponentSum (3 * N) (N + N * N) := by
      rw [card_coordinateIndex, Config.card_wallIndex]

theorem unsliced_parameters_half_range {N : ℕ} (hN : 5 ≤ N) :
    3 * N ≤ (N + N * N + 1) / 2 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  nlinarith

/-- The factorial-sensitive binomial estimate on the unsliced `3N`
configuration space. -/
theorem algebraicComponentSum_polygon_le {N : ℕ} (hN : 5 ≤ N) :
    algebraicComponentSum (3 * N) (N + N * N) ≤
      (3 * N + 1 : ℝ) * (12 * N : ℝ) ^ (3 * N) := by
  have hm : 1 ≤ 3 * N := by omega
  have hraw := weighted_partial_choose_le
    (n := N + N * N + 1) (m := 3 * N) hm
      (unsliced_parameters_half_range hN)
  have hmR : 0 < (3 * N : ℝ) := by positivity
  have hratio :
      (((12 * (N + N * N + 1) : ℕ) : ℝ) / (3 * N : ℝ)) ≤
        (12 * N : ℝ) := by
    rw [div_le_iff₀ hmR]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hNR : (5 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc
    algebraicComponentSum (3 * N) (N + N * N) ≤
        (3 * N + 1 : ℝ) *
          ((((12 * (N + N * N + 1) : ℕ) : ℝ) ^ (3 * N)) /
            (3 * N : ℝ) ^ (3 * N)) := by
      simpa [algebraicComponentSum] using hraw
    _ = (3 * N + 1 : ℝ) *
          ((((12 * (N + N * N + 1) : ℕ) : ℝ) /
            (3 * N : ℝ)) ^ (3 * N)) := by rw [div_pow]
    _ ≤ (3 * N + 1 : ℝ) * (12 * N : ℝ) ^ (3 * N) := by
      gcongr

/-- Main finite upper certificate on the headline `N^{O(N)}` scale.  The only
hypotheses are the two typed external mathematical inputs above. -/
theorem boundedStickKnot_count_le_unsliced
    {N factor : ℕ} {KnotType : Type*} {stickNumber : KnotType → ℕ}
    (hN : 5 ≤ N)
    (semantic : StickKnotSemanticInput N KnotType stickNumber)
    (baroneBasu : DegreeFourComponentTheorem factor) :
    (Nat.card (BoundedStickKnot stickNumber N) : ℝ) ≤
      (3 * N + 1 : ℝ) * (12 * factor * N : ℝ) ^ (3 * N) := by
  calc
    (Nat.card (BoundedStickKnot stickNumber N) : ℝ) ≤
        (factor : ℝ) ^ (3 * N) *
          algebraicComponentSum (3 * N) (N + N * N) :=
      boundedStickKnot_count_le_algebraicSum semantic baroneBasu
    _ ≤ (factor : ℝ) ^ (3 * N) *
          ((3 * N + 1 : ℝ) * (12 * N : ℝ) ^ (3 * N)) := by
      gcongr
      exact algebraicComponentSum_polygon_le hN
    _ = (3 * N + 1 : ℝ) * (12 * factor * N : ℝ) ^ (3 * N) := by
      rw [mul_pow]
      ring

end

end StickKnots
