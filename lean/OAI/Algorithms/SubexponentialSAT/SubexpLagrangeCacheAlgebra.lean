import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing

namespace OAI.Algorithms

/-!
# Algebra for the product-based Lagrange cache

The cache first multiplies the monic linear factors and their scalar
denominators, then applies one scalar inverse. These identities identify
that result with `TableInterpolation.basis` in the coefficient ring itself.
The coefficient statements use ordinary polynomial indices, starting with
the constant coefficient at index zero.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace SubexponentialSAT.SubexpLagrangeCacheAlgebra

variable {R : Type*} [CommRing R]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The unscaled product stored for one interpolation label. -/
def numerator (v : ι → R) (i : ι) : R[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (v j))

/-- The scalar denominator accumulated over the same labels. -/
def denominator (v : ι → R) (i : ι) : R :=
  ∏ j ∈ Finset.univ.erase i, (v i - v j)

/-- A proof-side inverse obtained by multiplying the individual inverses. -/
def inverseProduct (v : ι → R) (hu : TableInterpolation.UnitDifferences v)
    (i : ι) : R :=
  ∏ j ∈ Finset.univ.erase i, TableInterpolation.invDiff v hu i j

theorem numerator_natDegree_le (v : ι → R) (i : ι) :
    (numerator v i).natDegree ≤ Fintype.card ι - 1 := by
  calc
    (numerator v i).natDegree ≤
        ∑ j ∈ Finset.univ.erase i, (X - C (v j) : R[X]).natDegree :=
      Polynomial.natDegree_prod_le (Finset.univ.erase i)
        (fun j => (X - C (v j) : R[X]))
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 :=
      Finset.sum_le_sum fun j _ => Polynomial.natDegree_X_sub_C_le (v j)
    _ = Fintype.card ι - 1 := by simp

theorem numerator_natDegree_lt {p : ℕ} (hp : 0 < p)
    (v : Fin p → R) (i : Fin p) :
    (numerator v i).natDegree < p := by
  have h := numerator_natDegree_le v i
  simp only [Fintype.card_fin] at h
  omega

theorem numerator_coeff_eq_zero {p : ℕ} (hp : 0 < p)
    (v : Fin p → R) (i : Fin p) {j : ℕ} (hj : p ≤ j) :
    (numerator v i).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((numerator_natDegree_lt hp v i).trans_le hj)

@[simp] theorem numerator_eval_self (v : ι → R) (i : ι) :
    (numerator v i).eval (v i) = denominator v i := by
  simp [numerator, denominator, Polynomial.eval_prod]

theorem denominator_isUnit (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (i : ι) :
    IsUnit (denominator v i) := by
  apply IsUnit.prod_iff.mpr
  intro j hj
  exact hu i j (Finset.ne_of_mem_erase hj).symm

theorem inverseProduct_mul_denominator (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (i : ι) :
    inverseProduct v hu i * denominator v i = 1 := by
  rw [inverseProduct, denominator, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j hj
  exact TableInterpolation.invDiff_mul v hu (Finset.ne_of_mem_erase hj).symm

theorem basis_factorization (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (i : ι) :
    TableInterpolation.basis v hu i =
      C (inverseProduct v hu i) * numerator v i := by
  simp only [TableInterpolation.basis, TableInterpolation.basisDivisor,
    inverseProduct, numerator, map_prod, Finset.prod_mul_distrib]

/-- Any computed inverse of the accumulated denominator gives the exact
Lagrange basis. No choice of the individual inverses enters this premise. -/
theorem scaled_numerator_eq_basis (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (i : ι) (d : R)
    (hd : d * denominator v i = 1) :
    C d * numerator v i = TableInterpolation.basis v hu i := by
  have hi : denominator v i * inverseProduct v hu i = 1 := by
    rw [mul_comm]
    exact inverseProduct_mul_denominator v hu i
  have he : d = inverseProduct v hu i := left_inv_eq_right_inv hd hi
  rw [he]
  exact (basis_factorization v hu i).symm

/-- The dense cache stores coefficient zero first. -/
theorem scaled_numerator_coeff (v : ι → R)
    (hu : TableInterpolation.UnitDifferences v) (i : ι) (d : R)
    (hd : d * denominator v i = 1) (j : ℕ) :
    d * (numerator v i).coeff j =
      (TableInterpolation.basis v hu i).coeff j := by
  have h := congrArg (fun f : R[X] => f.coeff j)
    (scaled_numerator_eq_basis v hu i d hd)
  simpa only [Polynomial.coeff_C_mul] using h

/-- A unit denominator has nonzero image in every nontrivial target ring. -/
theorem denominator_map_ne_zero {S : Type*} [CommRing S] [Nontrivial S]
    (v : ι → R) (hu : TableInterpolation.UnitDifferences v) (i : ι)
    (φ : R →+* S) : φ (denominator v i) ≠ 0 :=
  ((denominator_isUnit v hu i).map φ).ne_zero

section OrderedTraversal

variable {M : Type*} [CommMonoid M]

/-- Product in traversal order, omitting the distinguished label. -/
def orderedProduct (f : ι → M) (i : ι) (js : List ι) : M :=
  ((js.filter fun j => decide (j ≠ i)).map f).prod

omit [Fintype ι] in
theorem orderedProduct_append (f : ι → M) (i : ι) (js ks : List ι) :
    orderedProduct f i (js ++ ks) = orderedProduct f i js * orderedProduct f i ks := by
  simp [orderedProduct]

/- Loop invariant for any processed prefix and any initial accumulator. -/
omit [Fintype ι] in
theorem foldl_skip_eq (f : ι → M) (i : ι) (js : List ι) (a : M) :
    js.foldl (fun acc j => if j = i then acc else acc * f j) a =
      a * orderedProduct f i js := by
  induction js generalizing a with
  | nil => simp [orderedProduct]
  | cons j js ih =>
      rw [List.foldl_cons, ih]
      by_cases h : j = i <;> simp [orderedProduct, h, mul_assoc]

theorem orderedProduct_finRange {p : ℕ} (f : Fin p → M) (i : Fin p) :
    orderedProduct f i (List.finRange p) = ∏ j ∈ Finset.univ.erase i, f j := by
  unfold orderedProduct
  rw [← List.prod_toFinset f (List.Nodup.filter _ (List.nodup_finRange p))]
  apply Finset.prod_congr
  · ext j
    simp
  · intro j _
    rfl

end OrderedTraversal

/-- The actual increasing-label traversal produces the same numerator. -/
theorem numerator_ordered {p : ℕ} (v : Fin p → R) (i : Fin p) :
    (((List.finRange p).filter fun j => decide (j ≠ i)).map
      fun j => X - C (v j)).prod = numerator v i :=
  orderedProduct_finRange (fun j => X - C (v j)) i

/-- The actual increasing-label traversal produces the same denominator. -/
theorem denominator_ordered {p : ℕ} (v : Fin p → R) (i : Fin p) :
    (((List.finRange p).filter fun j => decide (j ≠ i)).map
      fun j => v i - v j).prod = denominator v i :=
  orderedProduct_finRange (fun j => v i - v j) i

theorem numerator_foldl {p : ℕ} (v : Fin p → R) (i : Fin p) (a : R[X]) :
    (List.finRange p).foldl
      (fun acc j => if j = i then acc else acc * (X - C (v j))) a =
      a * numerator v i := by
  rw [foldl_skip_eq, orderedProduct_finRange]
  rfl

theorem denominator_foldl {p : ℕ} (v : Fin p → R) (i : Fin p) (a : R) :
    (List.finRange p).foldl
      (fun acc j => if j = i then acc else acc * (v i - v j)) a =
      a * denominator v i := by
  rw [foldl_skip_eq, orderedProduct_finRange]
  rfl

section ActualRing

variable (p μ : ℕ) [Fact p.Prime]

/-- The labels used by the actual selected-quartic ring cache. -/
def integerNodes : Fin p → SubexpActualRing.Ring p μ := fun i => (i.val : _)

theorem integerNodes_units : TableInterpolation.UnitDifferences (integerNodes p μ) :=
  TableInterpolation.unitDifferences_lambda_integerLabels p μ
    (Fact.out : p.Prime) (SubexpActualRing.F p μ)

theorem actual_denominator_isUnit (i : Fin p) :
    IsUnit (denominator (integerNodes p μ) i) :=
  denominator_isUnit _ (integerNodes_units p μ) i

/-- The inverse routine's residue precondition follows from the actual
integer labels; it is not a separately supplied nonvanishing assumption. -/
theorem actual_denominator_rho_ne_zero (hμ : 0 < μ) (i : Fin p) :
    SubexpActualRing.rho p μ hμ (denominator (integerNodes p μ) i) ≠ 0 :=
  denominator_map_ne_zero _ (integerNodes_units p μ) i (SubexpActualRing.rho p μ hμ)

theorem actual_numerator_natDegree_lt (i : Fin p) :
    (numerator (integerNodes p μ) i).natDegree < p :=
  numerator_natDegree_lt (Fact.out : p.Prime).pos _ i

theorem actual_scaled_numerator_eq_basis (i : Fin p) (d : SubexpActualRing.Ring p μ)
    (hd : d * denominator (integerNodes p μ) i = 1) :
    C d * numerator (integerNodes p μ) i =
      TableInterpolation.basis (integerNodes p μ) (integerNodes_units p μ) i :=
  scaled_numerator_eq_basis _ (integerNodes_units p μ) i d hd

end ActualRing

end SubexponentialSAT.SubexpLagrangeCacheAlgebra

end

end OAI.Algorithms
