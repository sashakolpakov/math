import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Moments
import OAI.Algorithms.SubexponentialSAT.Separation
import OAI.Algorithms.SubexponentialSAT.SubexpSeparation
import OAI.Algorithms.SubexponentialSAT.SymbolicCost

namespace OAI.Algorithms

/-!
# Executable coordinate-label monomial weights

The supplied coordinate list, labels, and exponent array are ordinary input
data. The recursive programs below perform actual scalar multiplications and
return their count. No mathematical finite-set choice is used by the programs.
For a duplicate-free support and a retained exponent, at most 3D+1 scalar
multiplications are performed. This is a scalar-operation bound, not a
Turing-machine bound for evaluating an arbitrary supplied coefficient ring.
-/

namespace SubexponentialSAT.SubexpWeightCode

open scoped BigOperators

section Programs

variable {R : Type*}

/-- A linear power loop, counting its one scalar multiplication per step. -/
def powerWithCost [One R] [Mul R] (x : R) : ℕ → R × ℕ
  | 0 => (1, 0)
  | n + 1 =>
      let p := powerWithCost x n
      (p.1 * x, p.2 + 1)

@[simp] theorem powerWithCost_value [Monoid R] (x : R) (n : ℕ) :
    (powerWithCost x n).1 = x ^ n := by
  induction n with
  | zero => simp [powerWithCost]
  | succ n ih => simp [powerWithCost, ih, pow_succ]

@[simp] theorem powerWithCost_cost [One R] [Mul R] (x : R) (n : ℕ) :
    (powerWithCost x n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [powerWithCost, ih]

/-- Compute one monomial weight by traversing the supplied support list.
Each coordinate incurs its power-loop multiplications and one multiplication
into the product of the remaining coordinates. -/
def weightWithCost [One R] [Mul R] {D : ℕ} (x : Fin D → R) (a : Fin D → ℕ) :
    List (Fin D) → R × ℕ
  | [] => (1, 0)
  | i :: tail =>
      let p := powerWithCost (x i) (a i)
      let w := weightWithCost x a tail
      (p.1 * w.1, p.2 + w.2 + 1)

@[simp] theorem weightWithCost_value [Monoid R] {D : ℕ}
    (x : Fin D → R) (a : Fin D → ℕ) (support : List (Fin D)) :
    (weightWithCost x a support).1 =
      (support.map (fun i => x i ^ a i)).prod := by
  induction support with
  | nil => rfl
  | cons i tail ih => simp [weightWithCost, ih]

@[simp] theorem weightWithCost_cost [One R] [Mul R] {D : ℕ}
    (x : Fin D → R) (a : Fin D → ℕ) (support : List (Fin D)) :
    (weightWithCost x a support).2 = (support.map a).sum + support.length := by
  induction support with
  | nil => rfl
  | cons i tail ih => simp [weightWithCost, ih, Nat.add_assoc, Nat.add_left_comm]

/-- Reading the label and exponent arrays requires two entries per coordinate.
This separate index count does not classify array lookup as scalar arithmetic. -/
def inputReads {D : ℕ} (support : List (Fin D)) : ℕ := 2 * support.length

/-- Executable full-coordinate version, used for the unsplit moment weight. -/
def fullWeightWithCost [One R] [Mul R] {D : ℕ}
    (x : Fin D → R) (a : Fin D → ℕ) : R × ℕ :=
  weightWithCost x a (List.finRange D)

end Programs

section Correctness

variable {D : ℕ} {R : Type*} [CommMonoid R]

theorem weightWithCost_eq_finset (x : Fin D → R) (a : Fin D → ℕ)
    (support : List (Fin D)) (hn : support.Nodup) :
    (weightWithCost x a support).1 = ∏ i ∈ support.toFinset, x i ^ a i := by
  rw [weightWithCost_value]
  exact (List.prod_toFinset (fun i => x i ^ a i) hn).symm

theorem weightWithCost_eq_coordinateWeight
    (x : Fin D → R) (a : Fin D → ℕ)
    (support : List (Fin D)) (hn : support.Nodup) :
    (weightWithCost x a support).1 =
      Separation.coordinateWeight support.toFinset id a x :=
  weightWithCost_eq_finset x a support hn

theorem weightWithCost_eq_labeled_coordinateWeight {V : Type*}
    (label : V → R) (x : Fin D → V) (a : Fin D → ℕ)
    (support : List (Fin D)) (hn : support.Nodup) :
    (weightWithCost (fun i => label (x i)) a support).1 =
      Separation.coordinateWeight support.toFinset label a x :=
  weightWithCost_eq_finset (fun i => label (x i)) a support hn

theorem fullWeightWithCost_value (x : Fin D → R) (a : Fin D → ℕ) :
    (fullWeightWithCost x a).1 = ∏ i, x i ^ a i := by
  rw [fullWeightWithCost, weightWithCost_eq_finset x a _ (List.nodup_finRange D)]
  simp

theorem weightWithCost_append (x : Fin D → R) (a : Fin D → ℕ)
    (s t : List (Fin D)) :
    (weightWithCost x a (s ++ t)).1 =
      (weightWithCost x a s).1 * (weightWithCost x a t).1 := by
  simp

end Correctness

section Bounds

variable {D : ℕ} {R : Type*} [One R] [Mul R]

theorem exponent_le_total (a : Fin D → ℕ) (i : Fin D) :
    a i ≤ ∑ j, a j :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)

theorem retained_exponent_le (a : Fin D → ℕ)
    (ha : (∑ i, a i) ≤ 2 * D + 1) (i : Fin D) :
    a i ≤ 2 * D + 1 :=
  (exponent_le_total a i).trans ha

/-- A direct coordinatewise bound on the recorded scalar operation count. -/
theorem weightWithCost_cost_le_length (x : Fin D → R) (a : Fin D → ℕ)
    (support : List (Fin D)) (B : ℕ) (ha : ∀ i ∈ support, a i ≤ B) :
    (weightWithCost x a support).2 ≤ support.length * (B + 1) := by
  induction support with
  | nil => simp [weightWithCost]
  | cons i tail ih =>
    have hi := ha i List.mem_cons_self
    have ht := ih (fun j hj => ha j (List.mem_cons_of_mem i hj))
    simp only [weightWithCost, powerWithCost_cost, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem weightWithCost_cost_le_quadratic (x : Fin D → R) (a : Fin D → ℕ)
    (support : List (Fin D)) (hn : support.Nodup)
    (ha : ∀ i ∈ support, a i ≤ 2 * D + 1) :
    (weightWithCost x a support).2 ≤ D * (2 * D + 2) := by
  have hlen : support.length ≤ D := by simpa using hn.length_le_card
  exact (weightWithCost_cost_le_length x a support (2 * D + 1) ha).trans
    (Nat.mul_le_mul_right _ hlen)

/-- The retained total-degree bound gives a stronger linear operation bound. -/
theorem weightWithCost_cost_le_retained (x : Fin D → R) (a : Fin D → ℕ)
    (support : List (Fin D)) (hn : support.Nodup)
    (ha : (∑ i, a i) ≤ 2 * D + 1) :
    (weightWithCost x a support).2 ≤ 3 * D + 1 := by
  have hlen : support.length ≤ D := by simpa using hn.length_le_card
  have hsum : (support.map a).sum ≤ ∑ i, a i := by
    rw [← List.sum_toFinset a hn]
    exact Finset.sum_le_sum_of_subset support.toFinset.subset_univ
  rw [weightWithCost_cost]
  omega

theorem inputReads_le (support : List (Fin D)) (hn : support.Nodup) :
    inputReads support ≤ 2 * D := by
  have hlen : support.length ≤ D := by simpa using hn.length_le_card
  exact Nat.mul_le_mul_left 2 hlen

theorem fullWeightWithCost_cost (x : Fin D → R) (a : Fin D → ℕ) :
    (fullWeightWithCost x a).2 = (∑ i, a i) + D := by
  rw [fullWeightWithCost, weightWithCost_cost,
    ← List.sum_toFinset a (List.nodup_finRange D)]
  simp

theorem fullWeightWithCost_cost_le_retained (x : Fin D → R) (a : Fin D → ℕ)
    (ha : (∑ i, a i) ≤ 2 * D + 1) :
    (fullWeightWithCost x a).2 ≤ 3 * D + 1 :=
  weightWithCost_cost_le_retained x a _ (List.nodup_finRange D) ha

end Bounds

section MomentBridge

variable {D : ℕ} {R : Type*} [CommSemiring R]

theorem fullWeightWithCost_eq_momentWeight
    (x : Fin D → R) (a : Fin D →₀ ℕ) :
    (fullWeightWithCost x a).1 = Moments.weight a x := by
  rw [fullWeightWithCost_value, Moments.weight_eq_prod_univ]

theorem weightWithCost_eq_momentWeight_of_support
    (x : Fin D → R) (a : Fin D →₀ ℕ)
    (support : List (Fin D)) (hn : support.Nodup)
    (hcover : ∀ i ∈ a.support, i ∈ support) :
    (weightWithCost x a support).1 = Moments.weight a x := by
  rw [weightWithCost_eq_finset x a support hn]
  unfold Moments.weight
  symm
  apply Finset.prod_subset
  · intro i hi
    exact List.mem_toFinset.mpr (hcover i hi)
  · intro i hi hnot
    have hz : a i = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hz]

theorem retainedWeight_cost
    (x : Fin D → R) (a : Fin D →₀ ℕ)
    (support : List (Fin D)) (hn : support.Nodup)
    (ha : a ∈ Moments.retained (2 * D + 1)) :
    (weightWithCost x a support).2 ≤ 3 * D + 1 := by
  apply weightWithCost_cost_le_retained x a support hn
  simpa [Finsupp.sum_fintype] using (Moments.mem_retained _ a).mp ha

/-- The computed local weights split the full moment across any supplied
duplicate-free color lists and a duplicate-free complementary list. -/
theorem momentWeight_eq_computed_partition {r : ℕ}
    (groups : Fin r → List (Fin D)) (outside : List (Fin D))
    (hgroups : ∀ g, (groups g).Nodup) (hout : outside.Nodup)
    (hdisjoint : Pairwise (fun g h =>
      Disjoint (groups g).toFinset (groups h).toFinset))
    (houtside : outside.toFinset =
      (Finset.univ.biUnion (fun g => (groups g).toFinset))ᶜ)
    (x : Fin D → R) (a : Fin D →₀ ℕ) :
    Moments.weight a x =
      (weightWithCost x a outside).1 *
        ∏ g, (weightWithCost x a (groups g)).1 := by
  rw [SubexpSeparation.momentWeight_partition
    (fun g => (groups g).toFinset) hdisjoint]
  apply congrArg₂ (· * ·)
  · rw [weightWithCost_eq_finset x a outside hout, houtside]
    exact Finset.prod_coe_sort _ (fun i => x i ^ a i)
  · apply Finset.prod_congr rfl
    intro g hg
    rw [weightWithCost_eq_finset x a (groups g) (hgroups g)]
    exact Finset.prod_coe_sort _ (fun i => x i ^ a i)

end MomentBridge

section RawCoefficients

variable {D : ℕ} {R : Type*}

/-- An ordinary singleton coefficient list at the zero X,U,Z index. -/
def rawScalar (D : ℕ) (c : R) : SymbolicCost.CoeffList D R :=
  [(((fun _ => 0), (0, 0)), c)]

@[simp] theorem rawScalar_length (D : ℕ) (c : R) :
    (rawScalar D c).length = 1 := rfl

theorem rawScalar_denote [CommSemiring R] (D : ℕ) (c : R) :
    SymbolicCost.denote (rawScalar D c) =
      WeightedSupport.scalarHom (ι := Fin D) c := by
  have hz : (Finsupp.equivFunOnFinite.symm (fun _ : Fin D => 0) : Fin D →₀ ℕ) = 0 := by
    ext i
    rfl
  simp [rawScalar, SymbolicCost.denote, SymbolicCost.monomial, hz,
    WeightedSupport.scalarHom]

/-- Compute the scalar coefficient and emit its literal for the symbolic backend.
Literal construction adds no scalar multiplications to the power/product loop. -/
def rawWeightWithCost [One R] [Mul R] (x : Fin D → R) (a : Fin D → ℕ)
    (support : List (Fin D)) : SymbolicCost.CoeffList D R × ℕ :=
  let w := weightWithCost x a support
  (rawScalar D w.1, w.2)

@[simp] theorem rawWeightWithCost_length [One R] [Mul R]
    (x : Fin D → R) (a : Fin D → ℕ) (support : List (Fin D)) :
    (rawWeightWithCost x a support).1.length = 1 := rfl

@[simp] theorem rawWeightWithCost_cost [One R] [Mul R]
    (x : Fin D → R) (a : Fin D → ℕ) (support : List (Fin D)) :
    (rawWeightWithCost x a support).2 = (weightWithCost x a support).2 := rfl

theorem rawWeightWithCost_denote [CommSemiring R]
    (x : Fin D → R) (a : Fin D → ℕ) (support : List (Fin D)) :
    SymbolicCost.denote (rawWeightWithCost x a support).1 =
      WeightedSupport.scalarHom (ι := Fin D) (weightWithCost x a support).1 :=
  rawScalar_denote D _

theorem rawWeightWithCost_coordinateWeight [CommSemiring R]
    (x : Fin D → R) (a : Fin D → ℕ) (support : List (Fin D)) (hn : support.Nodup) :
    SymbolicCost.denote (rawWeightWithCost x a support).1 =
      WeightedSupport.scalarHom (ι := Fin D)
        (Separation.coordinateWeight support.toFinset id a x) := by
  rw [rawWeightWithCost_denote, weightWithCost_eq_coordinateWeight x a support hn]

theorem rawWeightWithCost_cost_le_retained [One R] [Mul R]
    (x : Fin D → R) (a : Fin D → ℕ) (support : List (Fin D)) (hn : support.Nodup)
    (ha : (∑ i, a i) ≤ 2 * D + 1) :
    (rawWeightWithCost x a support).2 ≤ 3 * D + 1 :=
  weightWithCost_cost_le_retained x a support hn ha

end RawCoefficients

end SubexponentialSAT.SubexpWeightCode

end OAI.Algorithms
