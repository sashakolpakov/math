import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.MonomialCount
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-!
# Explicit lists for canonical symbolic coefficients

`project` scans a finite term list once for each supplied retained slot. Multiplication
first enumerates all input pairs and then projects. Duplicates are intentionally
allowed before projection. The counters below count scalar/index operations, not
primitive bit-machine steps; the latter need an implementation of the coefficient
ring and exponent vectors.
-/

namespace SubexponentialSAT.SymbolicCost

abbrev RawIndex (D : ℕ) := (Fin D → ℕ) × (ℕ × ℕ)
abbrev CoeffList (D : ℕ) (R : Type*) := List (RawIndex D × R)

/-- The actual three cutoffs for the manuscript's canonical representative. -/
def Retained (D : ℕ) (a : RawIndex D) : Prop :=
  (∑ i, a.1 i) ≤ 2 * D + 1 ∧ a.2.1 < D + 1 ∧ a.2.2 < D

instance retainedDecidable (D : ℕ) (a : RawIndex D) : Decidable (Retained D a) := by
  unfold Retained
  infer_instance

/-- Convert a mathematically retained monomial to the executable array index. -/
def slotIndex {D : ℕ} (a : SubexponentialSAT.MonomialCount.RetainedMonomial D) : RawIndex D :=
  (fun i => a.1.1 i, (a.2.1.val, a.2.2.val))

theorem slotIndex_injective {D : ℕ} : Function.Injective (@slotIndex D) := by
  intro a b h
  rcases a with ⟨⟨a, ha⟩, j, r⟩
  rcases b with ⟨⟨b, hb⟩, k, s⟩
  simp only [slotIndex, Prod.mk.injEq] at h
  have hab : a = b := Finsupp.ext (fun i => congrFun h.1 i)
  have hjk : j = k := Fin.ext h.2.1
  have hrs : r = s := Fin.ext h.2.2
  subst b
  subst k
  subst s
  rfl

theorem retained_slotIndex {D : ℕ} (a : SubexponentialSAT.MonomialCount.RetainedMonomial D) :
    Retained D (slotIndex a) := by
  refine ⟨?_, a.2.1.isLt, a.2.2.isLt⟩
  change (∑ i, a.1.1 i) ≤ 2 * D + 1
  simpa [Finsupp.sum_fintype] using a.1.2

theorem exists_slotIndex {D : ℕ} (a : RawIndex D) (ha : Retained D a) :
    ∃ s : SubexponentialSAT.MonomialCount.RetainedMonomial D, slotIndex s = a := by
  let e : SubexponentialSAT.MonomialCount.RetainedX D :=
    ⟨Finsupp.equivFunOnFinite.symm a.1, by simpa [Finsupp.sum_fintype] using ha.1⟩
  exact ⟨(e, (⟨a.2.1, ha.2.1⟩, ⟨a.2.2, ha.2.2⟩)), rfl⟩

/-- The enumerator is explicit input data. Its generation cost is not asserted
here: each executable operation below works for every complete duplicate-free list. -/
structure SlotEnumeration (D : ℕ) where
  entries : List (SubexponentialSAT.MonomialCount.RetainedMonomial D)
  nodup : entries.Nodup
  complete : ∀ a, a ∈ entries

def SlotEnumeration.slots {D : ℕ} (e : SlotEnumeration D) : List (RawIndex D) :=
  e.entries.map slotIndex

theorem SlotEnumeration.slots_nodup {D : ℕ} (e : SlotEnumeration D) :
    e.slots.Nodup := e.nodup.map slotIndex_injective

theorem SlotEnumeration.mem_slots {D : ℕ} (e : SlotEnumeration D) (a : RawIndex D) :
    a ∈ e.slots ↔ Retained D a := by
  constructor
  · intro h
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
    exact retained_slotIndex s
  · intro h
    obtain ⟨s, rfl⟩ := exists_slotIndex a h
    exact List.mem_map.mpr ⟨s, e.complete s, rfl⟩

theorem SlotEnumeration.length_slots {D : ℕ} (e : SlotEnumeration D) :
    e.slots.length = Fintype.card (SubexponentialSAT.MonomialCount.RetainedMonomial D) := by
  classical
  have h : e.entries.toFinset = Finset.univ := by
    ext a
    simp [e.complete a]
  rw [SlotEnumeration.slots, List.length_map, ← List.toFinset_card_of_nodup e.nodup,
    h, Finset.card_univ]

section Operations

variable {D : ℕ} {R : Type*} [Semiring R]

/-- A dense list contains every supplied slot once, in the supplied order,
including slots whose coefficients are zero. -/
def Dense (slots : List (RawIndex D)) (P : CoeffList D R) : Prop :=
  P.map Prod.fst = slots

omit [Semiring R] in
theorem Dense.length {slots : List (RawIndex D)} {P : CoeffList D R}
    (h : Dense slots P) : P.length = slots.length := by
  simpa [Dense] using congrArg List.length h

omit [Semiring R] in
theorem Dense.mem {slots : List (RawIndex D)} {P : CoeffList D R}
    (h : Dense slots P) {a : RawIndex D × R} (ha : a ∈ P) : a.1 ∈ slots := by
  rw [← h]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- Sum every occurrence of the requested coefficient by a sequential scan. -/
def coeff : CoeffList D R → RawIndex D → R
  | [], _ => 0
  | (a, c) :: tail, b => (if a = b then c else 0) + coeff tail b

/-- Retain the supplied slots, with all duplicate coefficients collected. -/
def project (slots : List (RawIndex D)) (P : CoeffList D R) : CoeffList D R :=
  slots.map fun a => (a, coeff P a)

/-- One explicit row of the pair-product enumeration. -/
def rowMul (p : RawIndex D × R) (Q : CoeffList D R) : CoeffList D R :=
  Q.map fun q => (p.1 + q.1, p.2 * q.2)

/-- Enumerate all input pairs; this is an ordinary terminating list recursion. -/
def rawMul : CoeffList D R → CoeffList D R → CoeffList D R
  | [], _ => []
  | p :: tail, Q => rowMul p Q ++ rawMul tail Q

def denseAdd (slots : List (RawIndex D)) (P Q : CoeffList D R) : CoeffList D R :=
  project slots (P ++ Q)

def denseMul (slots : List (RawIndex D)) (P Q : CoeffList D R) : CoeffList D R :=
  project slots (rawMul P Q)

theorem project_dense (slots : List (RawIndex D)) (P : CoeffList D R) :
    Dense slots (project slots P) := by simp [Dense, project, List.map_map, Function.comp_def]

theorem denseAdd_dense (slots : List (RawIndex D)) (P Q : CoeffList D R) :
    Dense slots (denseAdd slots P Q) := project_dense _ _

theorem denseMul_dense (slots : List (RawIndex D)) (P Q : CoeffList D R) :
    Dense slots (denseMul slots P Q) := project_dense _ _

omit [Semiring R] in
theorem Dense.retained (e : SlotEnumeration D) {P : CoeffList D R}
    (h : Dense e.slots P) {a : RawIndex D × R} (ha : a ∈ P) : Retained D a.1 :=
  (e.mem_slots a.1).mp (h.mem ha)

@[simp] theorem length_project (slots : List (RawIndex D)) (P : CoeffList D R) :
    (project slots P).length = slots.length := by simp [project]

@[simp] theorem length_rowMul (p : RawIndex D × R) (Q : CoeffList D R) :
    (rowMul p Q).length = Q.length := by simp [rowMul]

@[simp] theorem length_rawMul (P Q : CoeffList D R) :
    (rawMul P Q).length = P.length * Q.length := by
  induction P with
  | nil => simp [rawMul]
  | cons p P ih => simp [rawMul, ih, Nat.add_mul, Nat.add_comm]

@[simp] theorem coeff_append (P Q : CoeffList D R) (a : RawIndex D) :
    coeff (P ++ Q) a = coeff P a + coeff Q a := by
  induction P with
  | nil => simp [coeff]
  | cons p P ih => cases p; simp [coeff, ih, add_assoc]

@[simp] theorem coeff_project (slots : List (RawIndex D))
    (hn : slots.Nodup) (P : CoeffList D R) (a : RawIndex D) :
    coeff (project slots P) a = if a ∈ slots then coeff P a else 0 := by
  induction slots with
  | nil => simp [project, coeff]
  | cons b slots ih =>
    have hb : b ∉ slots := (List.nodup_cons.mp hn).1
    have hs : slots.Nodup := (List.nodup_cons.mp hn).2
    by_cases hba : b = a
    · subst b
      change (if a = a then coeff P a else 0) + coeff (project slots P) a = _
      rw [ih hs]
      simp [hb]
    · have hab : a ≠ b := Ne.symm hba
      change (if b = a then coeff P b else 0) + coeff (project slots P) a = _
      rw [ih hs]
      simp [hba, hab]

@[simp] theorem coeff_denseAdd (slots : List (RawIndex D))
    (hn : slots.Nodup) (P Q : CoeffList D R) (a : RawIndex D) :
    coeff (denseAdd slots P Q) a =
      if a ∈ slots then coeff P a + coeff Q a else 0 := by
  simp [denseAdd, coeff_project slots hn]

end Operations

section MeasuredOperations

variable {D : ℕ} {R : Type*} [Semiring R]

/-- Instrumented coefficient scan. Each cell charges a list visit, an index
comparison, and a scalar addition (including addition of zero). -/
def scanWithCost : CoeffList D R → RawIndex D → R × ℕ
  | [], _ => (0, 0)
  | (a, c) :: tail, b =>
    let rest := scanWithCost tail b
    ((if a = b then c else 0) + rest.1, rest.2 + 3)

theorem scanWithCost_eq (P : CoeffList D R) (a : RawIndex D) :
    scanWithCost P a = (coeff P a, 3 * P.length) := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rcases p with ⟨b, c⟩
    simp [scanWithCost, coeff, ih, Nat.mul_add]

/-- Append with one charged list copy per cell of its left input. -/
def appendWithCost {α : Type*} : List α → List α → List α × ℕ
  | [], Q => (Q, 0)
  | p :: P, Q =>
    let rest := appendWithCost P Q
    (p :: rest.1, rest.2 + 1)

theorem appendWithCost_eq {α : Type*} (P Q : List α) :
    appendWithCost P Q = (P ++ Q, P.length) := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [appendWithCost, ih]

/-- Each pair charges one exponent addition, one scalar multiplication,
and one list-cell construction. -/
def rowMulWithCost (p : RawIndex D × R) : CoeffList D R → CoeffList D R × ℕ
  | [] => ([], 0)
  | q :: Q =>
    let rest := rowMulWithCost p Q
    ((p.1 + q.1, p.2 * q.2) :: rest.1, rest.2 + 3)

theorem rowMulWithCost_eq (p : RawIndex D × R) (Q : CoeffList D R) :
    rowMulWithCost p Q = (rowMul p Q, 3 * Q.length) := by
  induction Q with
  | nil => rfl
  | cons q Q ih => simp [rowMulWithCost, rowMul, ih, Nat.mul_add]

/-- The outer multiplication loop also charges each row visit and the copies
performed by append. The result is the same raw pair enumeration as above. -/
def rawMulWithCost : CoeffList D R → CoeffList D R → CoeffList D R × ℕ
  | [], _ => ([], 0)
  | p :: P, Q =>
    let row := rowMulWithCost p Q
    let rest := rawMulWithCost P Q
    let joined := appendWithCost row.1 rest.1
    (joined.1, row.2 + rest.2 + joined.2 + 1)

theorem rawMulWithCost_eq (P Q : CoeffList D R) :
    rawMulWithCost P Q = (rawMul P Q, 4 * P.length * Q.length + P.length) := by
  induction P with
  | nil => simp [rawMulWithCost, rawMul]
  | cons p P ih =>
    simp only [rawMulWithCost, rowMulWithCost_eq, ih, appendWithCost_eq, rawMul, length_rowMul, List.length_cons]
    congr 1
    ring

/-- Projection really performs one complete coefficient scan per output slot.
Two additional events visit the slot and construct its output cell. -/
def projectWithCost : List (RawIndex D) → CoeffList D R → CoeffList D R × ℕ
  | [], _ => ([], 0)
  | a :: slots, P =>
    let c := scanWithCost P a
    let rest := projectWithCost slots P
    ((a, c.1) :: rest.1, c.2 + rest.2 + 2)

theorem projectWithCost_eq (slots : List (RawIndex D)) (P : CoeffList D R) :
    projectWithCost slots P = (project slots P, slots.length * (3 * P.length + 2)) := by
  induction slots with
  | nil => simp [projectWithCost, project]
  | cons a slots ih =>
    simp only [projectWithCost, scanWithCost_eq, ih,
      project, List.map_cons, List.length_cons]
    congr 1
    ring

def denseAddWithCost (slots : List (RawIndex D)) (P Q : CoeffList D R) :
    CoeffList D R × ℕ :=
  let joined := appendWithCost P Q
  let projected := projectWithCost slots joined.1
  (projected.1, joined.2 + projected.2)

def denseMulWithCost (slots : List (RawIndex D)) (P Q : CoeffList D R) :
    CoeffList D R × ℕ :=
  let pairs := rawMulWithCost P Q
  let projected := projectWithCost slots pairs.1
  (projected.1, pairs.2 + projected.2)

theorem denseAddWithCost_eq (slots : List (RawIndex D)) (P Q : CoeffList D R) :
    denseAddWithCost slots P Q =
      (denseAdd slots P Q, P.length + slots.length * (3 * (P.length + Q.length) + 2)) := by
  simp [denseAddWithCost, appendWithCost_eq, projectWithCost_eq, denseAdd]

theorem denseMulWithCost_eq (slots : List (RawIndex D)) (P Q : CoeffList D R) :
    denseMulWithCost slots P Q =
      (denseMul slots P Q,
        4 * P.length * Q.length + P.length +
          slots.length * (3 * (P.length * Q.length) + 2)) := by
  simp [denseMulWithCost, rawMulWithCost_eq, projectWithCost_eq, denseMul]

end MeasuredOperations

section CostBounds

/-- Exact abstract-operation budget for multiplying two dense N-slot lists.
These events are scalar operations, exponent operations, and list visits/copies;
none is being identified with a primitive bit-machine transition. -/
def denseCost (N : ℕ) : ℕ := 3 * N ^ 3 + 4 * N ^ 2 + 3 * N

def denseAddCost (N : ℕ) : ℕ := 6 * N ^ 2 + 3 * N

theorem denseMulWithCost_dense {D : ℕ} {R : Type*} [Semiring R]
    (slots : List (RawIndex D)) (P Q : CoeffList D R)
    (hP : P.length = slots.length) (hQ : Q.length = slots.length) :
    denseMulWithCost slots P Q = (denseMul slots P Q, denseCost slots.length) := by
  rw [denseMulWithCost_eq, hP, hQ]
  congr 1
  simp only [denseCost]
  ring

theorem denseAddWithCost_dense {D : ℕ} {R : Type*} [Semiring R]
    (slots : List (RawIndex D)) (P Q : CoeffList D R)
    (hP : P.length = slots.length) (hQ : Q.length = slots.length) :
    denseAddWithCost slots P Q = (denseAdd slots P Q, denseAddCost slots.length) := by
  rw [denseAddWithCost_eq, hP, hQ]
  congr 1
  simp only [denseAddCost]
  ring

theorem denseCost_le (N : ℕ) : denseCost N ≤ 10 * (N + 1) ^ 3 := by
  unfold denseCost
  have h1 : N ≤ (N + 1) ^ 3 := by
    calc
      N ≤ N + 1 := Nat.le_succ N
      _ ≤ (N + 1) ^ 3 := Nat.le_pow (by decide)
  have h2 : N ^ 2 ≤ (N + 1) ^ 3 := by
    apply (Nat.pow_le_pow_left (Nat.le_succ N) 2).trans
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : N ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ N) 3
  omega

theorem denseAddCost_le (N : ℕ) : denseAddCost N ≤ 10 * (N + 1) ^ 3 := by
  unfold denseAddCost
  have h1 : N ≤ (N + 1) ^ 3 := by
    calc
      N ≤ N + 1 := Nat.le_succ N
      _ ≤ (N + 1) ^ 3 := Nat.le_pow (by decide)
  have h2 : N ^ 2 ≤ (N + 1) ^ 3 := by
    apply (Nat.pow_le_pow_left (Nat.le_succ N) 2).trans
    exact Nat.pow_le_pow_right (by omega) (by decide)
  omega

def symbolicFactor (D : ℕ) : ℕ := 10 * (D * (D + 1) + 1) ^ 3

theorem ten_cube_le_factor (D M : ℕ) (hM : 1 ≤ M) :
    10 * (M * ((D + 1) * D) + 1) ^ 3 ≤ symbolicFactor D * M ^ 4 := by
  have hbase : M * ((D + 1) * D) + 1 ≤ M * (D * (D + 1) + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have h : (D + 1) * D = D * (D + 1) := Nat.mul_comm _ _
    rw [h]
    omega
  calc
    10 * (M * ((D + 1) * D) + 1) ^ 3 ≤
        10 * (M * (D * (D + 1) + 1)) ^ 3 :=
      Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left hbase 3)
    _ = symbolicFactor D * M ^ 3 := by simp only [symbolicFactor]; ring
    _ ≤ symbolicFactor D * M ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM (by decide))

theorem retainedX_pos (D : ℕ) :
    1 ≤ Fintype.card (SubexponentialSAT.MonomialCount.RetainedX D) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨0, by simp⟩⟩

/-- Conservative polynomial-in-D times M_X^4 bound, derived from the
instrumented list multiplication and the actual retained-slot cardinality. -/
theorem denseCost_retained_le (D : ℕ) :
    denseCost (Fintype.card (SubexponentialSAT.MonomialCount.RetainedMonomial D)) ≤
      symbolicFactor D * Fintype.card (SubexponentialSAT.MonomialCount.RetainedX D) ^ 4 := by
  apply (denseCost_le _).trans
  simp only [SubexponentialSAT.MonomialCount.RetainedMonomial, Fintype.card_prod,
    SubexponentialSAT.MonomialCount.UZIndices, Fintype.card_fin]
  exact ten_cube_le_factor D _ (retainedX_pos D)

theorem denseAddCost_retained_le (D : ℕ) :
    denseAddCost (Fintype.card (SubexponentialSAT.MonomialCount.RetainedMonomial D)) ≤
      symbolicFactor D * Fintype.card (SubexponentialSAT.MonomialCount.RetainedX D) ^ 4 := by
  apply (denseAddCost_le _).trans
  simp only [SubexponentialSAT.MonomialCount.RetainedMonomial, Fintype.card_prod,
    SubexponentialSAT.MonomialCount.UZIndices, Fintype.card_fin]
  exact ten_cube_le_factor D _ (retainedX_pos D)

/-- The bound applies to the cost returned by the actual executable operation,
for an arbitrary supplied complete ordering of the retained slots. -/
theorem denseMulWithCost_bound {D : ℕ} {R : Type*} [Semiring R]
    (e : SlotEnumeration D) (P Q : CoeffList D R)
    (hP : P.length = e.slots.length) (hQ : Q.length = e.slots.length) :
    (denseMulWithCost e.slots P Q).2 ≤
      symbolicFactor D * Fintype.card (SubexponentialSAT.MonomialCount.RetainedX D) ^ 4 := by
  rw [denseMulWithCost_dense _ _ _ hP hQ, e.length_slots]
  exact denseCost_retained_le D

theorem denseAddWithCost_bound {D : ℕ} {R : Type*} [Semiring R]
    (e : SlotEnumeration D) (P Q : CoeffList D R)
    (hP : P.length = e.slots.length) (hQ : Q.length = e.slots.length) :
    (denseAddWithCost e.slots P Q).2 ≤
      symbolicFactor D * Fintype.card (SubexponentialSAT.MonomialCount.RetainedX D) ^ 4 := by
  rw [denseAddWithCost_dense _ _ _ hP hQ, e.length_slots]
  exact denseAddCost_retained_le D

end CostBounds

section PolynomialSemantics

variable {D : ℕ} {R : Type*} [CommSemiring R]

abbrev Poly (D : ℕ) (R : Type*) [CommSemiring R] :=
  SubexponentialSAT.Truncation.Poly (Fin D) R

noncomputable def monomial (a : RawIndex D) (c : R) : Poly D R :=
  Polynomial.monomial a.2.1 (Polynomial.monomial a.2.2
    (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a.1) c))

noncomputable def denote : CoeffList D R → Poly D R
  | [] => 0
  | (a, c) :: tail => monomial a c + denote tail

noncomputable def polyCoeff (P : Poly D R) (a : RawIndex D) : R :=
  ((P.coeff a.2.1).coeff a.2.2).coeff (Finsupp.equivFunOnFinite.symm a.1)

@[simp] theorem polyCoeff_zero (a : RawIndex D) :
    polyCoeff (0 : Poly D R) a = 0 := by simp [polyCoeff]

@[simp] theorem polyCoeff_add (P Q : Poly D R) (a : RawIndex D) :
    polyCoeff (P + Q) a = polyCoeff P a + polyCoeff Q a := by simp [polyCoeff]

@[simp] theorem polyCoeff_monomial (a b : RawIndex D) (c : R) :
    polyCoeff (monomial a c) b = if a = b then c else 0 := by
  rcases a with ⟨a, j, r⟩
  rcases b with ⟨b, k, s⟩
  by_cases ha : a = b <;> by_cases hj : j = k <;> by_cases hr : r = s <;>
    simp [polyCoeff, monomial, Polynomial.coeff_monomial,
      MvPolynomial.coeff_monomial, ha, hj, hr ]

@[simp] theorem polyCoeff_denote (P : CoeffList D R) (a : RawIndex D) :
    polyCoeff (denote P) a = coeff P a := by
  induction P with
  | nil => simp [denote, coeff]
  | cons p P ih => cases p; simp [denote, coeff, ih]

@[simp] theorem denote_append (P Q : CoeffList D R) :
    denote (P ++ Q) = denote P + denote Q := by
  induction P with
  | nil => simp [denote]
  | cons p P ih => cases p; simp [denote, ih, add_assoc]

@[simp] theorem monomial_mul (a b : RawIndex D) (c d : R) :
    monomial (a + b) (c * d) = monomial a c * monomial b d := by
  have h : Finsupp.equivFunOnFinite.symm (a.1 + b.1) =
      Finsupp.equivFunOnFinite.symm a.1 + Finsupp.equivFunOnFinite.symm b.1 := by
    ext i
    rfl
  simp [monomial, Polynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial, h]

@[simp] theorem denote_rowMul (p : RawIndex D × R) (Q : CoeffList D R) :
    denote (rowMul p Q) = monomial p.1 p.2 * denote Q := by
  induction Q with
  | nil => simp [rowMul, denote]
  | cons q Q ih =>
    rcases q with ⟨a, c⟩
    change monomial (p.1 + a) (p.2 * c) + denote (rowMul p Q) = _
    rw [monomial_mul, ih]
    simp [denote, mul_add]

@[simp] theorem denote_rawMul (P Q : CoeffList D R) :
    denote (rawMul P Q) = denote P * denote Q := by
  induction P with
  | nil => simp [rawMul, denote]
  | cons p P ih =>
    rcases p with ⟨a, c⟩
    simp [rawMul, denote, ih, add_mul]

/-- All coefficients of the actual projected multiplication agree with full
polynomial multiplication at retained slots and vanish elsewhere. -/
theorem denseMul_correct (slots : List (RawIndex D)) (hn : slots.Nodup)
    (P Q : CoeffList D R) (a : RawIndex D) :
    polyCoeff (denote (denseMul slots P Q)) a =
      if a ∈ slots then polyCoeff (denote P * denote Q) a else 0 := by
  rw [polyCoeff_denote, denseMul, coeff_project slots hn]
  simp only [← polyCoeff_denote, denote_rawMul]

theorem polyCoeff_canonical (P : Poly D R) (a : RawIndex D) :
    polyCoeff (SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1) P) a =
      if Retained D a then polyCoeff P a else 0 := by
  rcases a with ⟨a, j, r⟩
  by_cases ha : (∑ i, a i) ≤ 2 * D + 1 <;>
    by_cases hj : j < D + 1 <;> by_cases hr : r < D <;>
    simp [polyCoeff, SubexponentialSAT.Truncation.coeff_canonical,
      SubexponentialSAT.Truncation.coeff_xTrunc, Finsupp.sum_fintype, Retained, ha, hj, hr]

/-- A list implementing the retained slots gives the genuine canonical
representative of the polynomial product. No quotient-ring evaluation is used. -/
theorem denseMul_denote (slots : List (RawIndex D)) (hn : slots.Nodup)
    (hslots : ∀ a, a ∈ slots ↔ Retained D a) (P Q : CoeffList D R) :
    denote (denseMul slots P Q) =
      SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1) (denote P * denote Q) := by
  ext j r a
  have h := denseMul_correct slots hn P Q (a, (j, r))
  simp only [hslots] at h
  have hc := polyCoeff_canonical (denote P * denote Q) (a, (j, r))
  exact (by simpa [polyCoeff] using h.trans hc.symm)

theorem denseAdd_denote (slots : List (RawIndex D)) (hn : slots.Nodup)
    (hslots : ∀ a, a ∈ slots ↔ Retained D a) (P Q : CoeffList D R) :
    denote (denseAdd slots P Q) =
      SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1) (denote P + denote Q) := by
  ext j r a
  have h := coeff_denseAdd slots hn P Q (a, (j, r))
  simp only [hslots] at h
  have hc := polyCoeff_canonical (denote P + denote Q) (a, (j, r))
  have h' : polyCoeff (denote (denseAdd slots P Q)) (a, (j, r)) =
      polyCoeff (SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1)
        (denote P + denote Q)) (a, (j, r)) := by
    rw [polyCoeff_denote]
    exact h.trans (by simpa only [polyCoeff_add, polyCoeff_denote] using hc.symm)
  simpa only [polyCoeff, Finsupp.equivFunOnFinite_symm_coe] using h'

theorem denseMulWithCost_correct (e : SlotEnumeration D) (P Q : CoeffList D R) :
    denote (denseMulWithCost e.slots P Q).1 =
      SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1) (denote P * denote Q) := by
  rw [denseMulWithCost_eq]
  exact denseMul_denote _ e.slots_nodup e.mem_slots P Q

theorem denseAddWithCost_correct (e : SlotEnumeration D) (P Q : CoeffList D R) :
    denote (denseAddWithCost e.slots P Q).1 =
      SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1) (denote P + denote Q) := by
  rw [denseAddWithCost_eq]
  exact denseAdd_denote _ e.slots_nodup e.mem_slots P Q

end PolynomialSemantics

end SubexponentialSAT.SymbolicCost
namespace SubexponentialSAT.SymbolicCost

/-- Actual serial data for an exponent index; the final entries are U and Z. -/
def indexData {D : ℕ} (a : RawIndex D) : List ℕ :=
  List.ofFn a.1 ++ [a.2.1, a.2.2]

@[simp] theorem length_indexData {D : ℕ} (a : RawIndex D) :
    (indexData a).length = D + 2 := by simp [indexData]

theorem indexData_injective {D : ℕ} : Function.Injective (@indexData D) := by
  intro a b h
  have hx := congrArg (List.take D) h
  have hy := congrArg (List.drop D) h
  have htake (a : RawIndex D) : (indexData a).take D = List.ofFn a.1 := by
    unfold indexData
    exact List.take_left' (by simp)
  simp only [htake] at hx
  have hx' : a.1 = b.1 := List.ofFn_injective hx
  simp [indexData] at hy
  exact Prod.ext hx' (Prod.ext hy.1 hy.2)

theorem indexData_bound {D : ℕ} (a : RawIndex D) (ha : Retained D a) :
    ∀ n ∈ indexData a, n ≤ 2 * D + 1 := by
  intro n hn
  simp only [indexData, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ha.1
  · rcases hn with rfl | rfl <;> have hj := ha.2.1 <;> have hr := ha.2.2 <;> omega

/-- Unary delimited encoding is sufficient for exponent indices, since their
values are O(D). Coefficients require a different (binary) encoding. -/
def unaryWord (n : ℕ) : List Bool := List.replicate n true ++ [false]

def unaryWords (xs : List ℕ) : List Bool := xs.flatMap unaryWord

def decodeUnary : List Bool → ℕ → List ℕ
  | [], _ => []
  | true :: bits, n => decodeUnary bits (n + 1)
  | false :: bits, n => n :: decodeUnary bits 0

theorem decodeUnary_word (n acc : ℕ) (bits : List Bool) :
    decodeUnary (unaryWord n ++ bits) acc = (acc + n) :: decodeUnary bits 0 := by
  induction n generalizing acc with
  | zero => simp [unaryWord, decodeUnary]
  | succ n ih =>
    simp only [unaryWord, List.replicate_succ, List.cons_append,
      List.append_assoc, decodeUnary]
    simpa [unaryWord, Nat.add_assoc, Nat.add_comm 1 n] using ih (acc + 1)

theorem decodeUnary_words (xs : List ℕ) : decodeUnary (unaryWords xs) 0 = xs := by
  induction xs with
  | nil => rfl
  | cons n ns ih =>
    change decodeUnary (unaryWord n ++ unaryWords ns) 0 = n :: ns
    rw [decodeUnary_word, Nat.zero_add, ih]

theorem unaryWords_injective : Function.Injective unaryWords := by
  intro a b h
  have hd := congrArg (fun bits => decodeUnary bits 0) h
  simpa only [decodeUnary_words] using hd

theorem unaryWords_length_le (xs : List ℕ) (B : ℕ) (h : ∀ n ∈ xs, n ≤ B) :
    (unaryWords xs).length ≤ xs.length * (B + 1) := by
  induction xs with
  | nil => simp [unaryWords]
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht := ih (fun m hm => h m (by simp [hm]))
    simp only [unaryWords, List.flatMap_cons, List.length_append, unaryWord,
      List.length_replicate, List.length_cons] at *
    simp only [List.length_nil] at *
    rw [Nat.add_mul]
    omega

def encodeIndex {D : ℕ} (a : RawIndex D) : List Bool := unaryWords (indexData a)

theorem encodeIndex_injective {D : ℕ} : Function.Injective (@encodeIndex D) :=
  unaryWords_injective.comp indexData_injective

theorem encodeIndex_length_le {D : ℕ} (a : RawIndex D) (ha : Retained D a) :
    (encodeIndex a).length ≤ (D + 2) * (2 * D + 2) := by
  have h := unaryWords_length_le (indexData a) (2 * D + 1) (indexData_bound a ha)
  simpa [encodeIndex] using h

/-- A concrete bit-by-bit equality scan; the counter records actual inspected
bit pairs plus its terminal inspection. It is not a compiled TM trace. -/
def equalBitsWithCost : List Bool → List Bool → Bool × ℕ
  | [], [] => (true, 1)
  | x :: xs, y :: ys =>
    if x = y then
      let rest := equalBitsWithCost xs ys
      (rest.1, rest.2 + 1)
    else (false, 1)
  | _, _ => (false, 1)

theorem equalBitsWithCost_correct (xs ys : List Bool) :
    (equalBitsWithCost xs ys).1 = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equalBitsWithCost]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equalBitsWithCost]
    | cons y ys =>
      by_cases h : x = y
      · simp [equalBitsWithCost, h, ih]
      · simp [equalBitsWithCost, h]

theorem equalBitsWithCost_le (xs ys : List Bool) :
    (equalBitsWithCost xs ys).2 ≤ xs.length + 1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equalBitsWithCost]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equalBitsWithCost]
    | cons y ys =>
      by_cases h : x = y
      · simpa [equalBitsWithCost, h] using Nat.add_le_add_right (ih ys) 1
      · simp [equalBitsWithCost, h]

theorem encodedIndexEquality_correct {D : ℕ} (a b : RawIndex D) :
    (equalBitsWithCost (encodeIndex a) (encodeIndex b)).1 = true ↔ a = b := by
  rw [equalBitsWithCost_correct]
  exact encodeIndex_injective.eq_iff

theorem encodedIndexEquality_cost {D : ℕ} (a b : RawIndex D) (ha : Retained D a) :
    (equalBitsWithCost (encodeIndex a) (encodeIndex b)).2 ≤
      (D + 2) * (2 * D + 2) + 1 :=
  (equalBitsWithCost_le _ _).trans (Nat.add_le_add_right (encodeIndex_length_le a ha) 1)

section EncodedScan

variable {D : ℕ} {R : Type*} [Semiring R]

def encodeTerms (P : CoeffList D R) : List (List Bool × R) :=
  P.map fun p => (encodeIndex p.1, p.2)

/-- A coefficient scan on stored bit-string keys. Only coefficient addition is
abstract here: index equality is performed by the explicit bit-by-bit routine.
The counter charges bit inspections, scalar additions, and list visits. -/
def encodedScan : List (List Bool × R) → List Bool → R × ℕ
  | [], _ => (0, 0)
  | (key, c) :: P, target =>
    let eq := equalBitsWithCost target key
    let rest := encodedScan P target
    ((if eq.1 = true then c else 0) + rest.1, eq.2 + rest.2 + 2)

theorem encodedScan_correct (P : CoeffList D R) (a : RawIndex D) :
    (encodedScan (encodeTerms P) (encodeIndex a)).1 = coeff P a := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rcases p with ⟨b, c⟩
    change (if (equalBitsWithCost (encodeIndex a) (encodeIndex b)).1 = true then c else 0) +
        (encodedScan (encodeTerms P) (encodeIndex a)).1 =
      (if b = a then c else 0) + coeff P a
    rw [ih]
    have hc : (equalBitsWithCost (encodeIndex a) (encodeIndex b)).1 = true ↔ b = a :=
      (encodedIndexEquality_correct a b).trans eq_comm
    simp only [hc]

theorem encodedScan_cost (P : List (List Bool × R)) (target : List Bool) :
    (encodedScan P target).2 ≤ P.length * (target.length + 3) := by
  induction P with
  | nil => simp [encodedScan]
  | cons p P ih =>
    rcases p with ⟨key, c⟩
    have he := equalBitsWithCost_le target key
    simp only [encodedScan, List.length_cons ]
    rw [Nat.add_mul]
    omega

theorem encodedScan_retained_cost (P : CoeffList D R) (a : RawIndex D)
    (ha : Retained D a) :
    (encodedScan (encodeTerms P) (encodeIndex a)).2 ≤
      P.length * ((D + 2) * (2 * D + 2) + 3) := by
  apply (encodedScan_cost _ _).trans
  simp only [encodeTerms, List.length_map]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (encodeIndex_length_le a ha) 3)

end EncodedScan

end SubexponentialSAT.SymbolicCost

end OAI.Algorithms
