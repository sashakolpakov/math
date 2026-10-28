import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SymbolicCost
import OAI.Algorithms.SubexponentialSAT.Counting
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Executable raw coefficient lists for marked incidence arguments

The executable definitions consume only a scalar beta and finite Taylor
coefficient arrays. They construct lists of explicit exponent indices and
scalars; no `Polynomial` occurs in an executable definition.
-/

namespace SubexponentialSAT.SubexpArgumentCode

open scoped BigOperators

/-- An index with no input-coordinate variables. -/
def constantIndex (D u z : ℕ) : SymbolicCost.RawIndex D :=
  (fun _ => 0, (u, z))

/-- The index of U^u Z^z X_i, represented by an actual finite coordinate function. -/
def coordinateIndex {D : ℕ} (i : Fin D) (u z : ℕ) : SymbolicCost.RawIndex D :=
  (fun v => if v = i then 1 else 0, (u, z))

/-- Emit one coefficient-list entry for each coordinate of one linear row. -/
def rawRow {D : ℕ} {A : Type*} (u z : ℕ) (a : Fin D → A) :
    SymbolicCost.CoeffList D A :=
  List.ofFn (fun i => (coordinateIndex i u z, a i))

/-- Compile beta + U(row_0 X - beta) + sum_{1<=j<=r} Z^j row_j X.
Zero coefficients are deliberately retained; no equality test on A is needed. -/
def compileArgument {D r : ℕ} {A : Type*} [Neg A]
    (β : A) (a : Fin (r + 1) → Fin D → A) : SymbolicCost.CoeffList D A :=
  [(constantIndex D 0 0, β), (constantIndex D 1 0, -β)] ++
    rawRow 1 0 (a 0) ++
    (List.ofFn (fun j : Fin r => rawRow 0 (j.val + 1) (a j.succ))).flatten

/-- Zero-extension of the supplied finite coefficient array. -/
def coefficientAt {D r : ℕ} {A : Type*} [Zero A]
    (a : Fin (r + 1) → Fin D → A) (j : ℕ) (i : Fin D) : A :=
  if h : j < r + 1 then a ⟨j, h⟩ i else 0

@[simp] theorem length_rawRow {D : ℕ} {A : Type*} (u z : ℕ) (a : Fin D → A) :
    (rawRow u z a).length = D := by simp [rawRow]

@[simp] theorem length_compileArgument {D r : ℕ} {A : Type*} [Neg A]
    (β : A) (a : Fin (r + 1) → Fin D → A) :
    (compileArgument β a).length = 2 + (r + 1) * D := by
  simp [compileArgument, List.length_flatten, List.map_ofFn, Fin.sum_ofFn]
  ring

theorem length_compileArgument_le {D r : ℕ} {A : Type*} [Neg A]
    (β : A) (a : Fin (r + 1) → Fin D → A) :
    (compileArgument β a).length ≤ 2 + (r + 1) * D :=
  le_of_eq (length_compileArgument β a)

@[simp] theorem coefficientAt_fin {D r : ℕ} {A : Type*} [Zero A]
    (a : Fin (r + 1) → Fin D → A) (j : Fin (r + 1)) (i : Fin D) :
    coefficientAt a j.val i = a j i := by simp [coefficientAt, j.isLt]

/- The following counter records declared source-level events. In a raw row,
three events mean coefficient lookup, index construction, and list-cell
construction. Appending counts each copied cell. This is not a bit-machine
cost, and producing the input Taylor coefficients is outside this compiler. -/

def tabulateWithCost {B : Type*} (events : ℕ) :
    (n : ℕ) → (Fin n → B) → List B × ℕ
  | 0, _ => ([], 0)
  | n + 1, f =>
    let rest := tabulateWithCost events n (fun i => f i.succ)
    (f 0 :: rest.1, rest.2 + events)

theorem tabulateWithCost_eq {B : Type*} (events n : ℕ) (f : Fin n → B) :
    tabulateWithCost events n f = (List.ofFn f, n * events) := by
  induction n with
  | zero => simp [tabulateWithCost]
  | succ n ih =>
    simp [tabulateWithCost, ih, List.ofFn_succ, Nat.add_mul]

def rawRowWithCost {D : ℕ} {A : Type*} (u z : ℕ) (a : Fin D → A) :
    SymbolicCost.CoeffList D A × ℕ :=
  tabulateWithCost 3 D (fun i => (coordinateIndex i u z, a i))

@[simp] theorem rawRowWithCost_eq {D : ℕ} {A : Type*}
    (u z : ℕ) (a : Fin D → A) :
    rawRowWithCost u z a = (rawRow u z a, 3 * D) := by
  simp [rawRowWithCost, rawRow, tabulateWithCost_eq, Nat.mul_comm]

/-- Execute each row compiler once and append its output, counting actual
copied cells and one loop event for each row. -/
def collectRowsWithCost {D : ℕ} {A : Type*} : (n : ℕ) →
    (Fin n → SymbolicCost.CoeffList D A × ℕ) → SymbolicCost.CoeffList D A × ℕ
  | 0, _ => ([], 0)
  | n + 1, f =>
    let first := f 0
    let rest := collectRowsWithCost n (fun i => f i.succ)
    let joined := SymbolicCost.appendWithCost first.1 rest.1
    (joined.1, first.2 + rest.2 + joined.2 + 1)

theorem collectRowsWithCost_eq {D : ℕ} {A : Type*}
    (n : ℕ) (f : Fin n → SymbolicCost.CoeffList D A × ℕ)
    (hlen : ∀ i, (f i).1.length = D) (hcost : ∀ i, (f i).2 = 3 * D) :
    collectRowsWithCost n f =
      ((List.ofFn (fun i => (f i).1)).flatten, n * (4 * D + 1)) := by
  induction n with
  | zero => simp [collectRowsWithCost]
  | succ n ih =>
    rw [collectRowsWithCost,
      ih (fun i => f i.succ) (fun i => hlen i.succ) (fun i => hcost i.succ)]
    simp only [SymbolicCost.appendWithCost_eq,
      List.ofFn_succ, List.flatten_cons, hlen, hcost]
    congr 1
    ring

def compileArgumentWithCost {D r : ℕ} {A : Type*} [Neg A]
    (β : A) (a : Fin (r + 1) → Fin D → A) : SymbolicCost.CoeffList D A × ℕ :=
  let first := rawRowWithCost 1 0 (a 0)
  let tail := collectRowsWithCost r
    (fun j => rawRowWithCost 0 (j.val + 1) (a j.succ))
  let joined := SymbolicCost.appendWithCost first.1 tail.1
  ((constantIndex D 0 0, β) :: (constantIndex D 1 0, -β) :: joined.1,
    first.2 + tail.2 + joined.2 + 3)

/-- Exact count of the declared construction events, alongside the actual output. -/
theorem compileArgumentWithCost_eq {D r : ℕ} {A : Type*} [Neg A]
    (β : A) (a : Fin (r + 1) → Fin D → A) :
    compileArgumentWithCost β a =
      (compileArgument β a, 4 * (r + 1) * D + r + 3) := by
  have ht := collectRowsWithCost_eq r
    (fun j : Fin r => rawRowWithCost 0 (j.val + 1) (a j.succ))
    (by intro j; simp) (by intro j; simp)
  simp only [rawRowWithCost_eq] at ht
  simp only [compileArgumentWithCost, ht, rawRowWithCost_eq,
    SymbolicCost.appendWithCost_eq, length_rawRow]
  apply Prod.ext
  · simp [compileArgument]
  · simp only
    ring

section Semantics

noncomputable section

variable {D r : ℕ} {A : Type*} [CommRing A]

/-- Mathematical meaning of a row from the finite Taylor array. -/
def semanticRow (a : Fin (r + 1) → Fin D → A) (j : ℕ) : MvPolynomial (Fin D) A :=
  WeightedSupport.linearForm Finset.univ (coefficientAt a j)

@[simp] theorem semanticRow_fin (a : Fin (r + 1) → Fin D → A) (j : Fin (r + 1)) :
    semanticRow a j.val = WeightedSupport.linearForm Finset.univ (a j) := by
  unfold semanticRow
  congr 1
  funext i
  exact coefficientAt_fin a j i

theorem exponent_coordinateIndex (i : Fin D) (u z : ℕ) :
    Finsupp.equivFunOnFinite.symm (coordinateIndex i u z).1 = Finsupp.single i 1 := by
  ext v
  simp [coordinateIndex, Finsupp.single_apply, eq_comm]

theorem exponent_constantIndex (u z : ℕ) :
    (Finsupp.equivFunOnFinite.symm (constantIndex D u z).1 : Fin D →₀ ℕ) = 0 := by
  ext v
  rfl

@[simp] theorem monomial_coordinateIndex (i : Fin D) (u z : ℕ) (c : A) :
    SymbolicCost.monomial (coordinateIndex i u z) c =
      Polynomial.monomial u (Polynomial.monomial z (MvPolynomial.monomial (Finsupp.single i 1) c)) := by
  simp only [SymbolicCost.monomial]
  rw [exponent_coordinateIndex]
  rfl

@[simp] theorem monomial_constantIndex (u z : ℕ) (c : A) :
    SymbolicCost.monomial (constantIndex D u z) c =
      Polynomial.monomial u (Polynomial.monomial z (MvPolynomial.C c)) := by
  simp only [SymbolicCost.monomial]
  rw [exponent_constantIndex]
  rfl

theorem denote_eq_sum (P : SymbolicCost.CoeffList D A) :
    SymbolicCost.denote P = (P.map (fun t => SymbolicCost.monomial t.1 t.2)).sum := by
  induction P with
  | nil => rfl
  | cons p P ih => cases p; simp [SymbolicCost.denote, ih]

@[simp] theorem denote_rawRow (u z : ℕ) (a : Fin D → A) :
    SymbolicCost.denote (rawRow u z a) =
      Polynomial.monomial u (Polynomial.monomial z (WeightedSupport.linearForm Finset.univ a)) := by
  rw [denote_eq_sum]
  simp [rawRow, List.map_ofFn, Fin.sum_ofFn, WeightedSupport.linearForm, map_sum]

@[simp] theorem denote_flatten (rows : List (SymbolicCost.CoeffList D A)) :
    SymbolicCost.denote rows.flatten = (rows.map SymbolicCost.denote).sum := by
  induction rows with
  | nil => rfl
  | cons p ps ih => simp [List.flatten_cons, SymbolicCost.denote_append, ih]

/-- Reindex the positive Taylor coefficients without introducing a polynomial oracle. -/
theorem sum_positive (f : ℕ → Truncation.Poly (Fin D) A) (r : ℕ) :
    (∑ j : Fin r, f (j.val + 1)) = ∑ j ∈ (Finset.range (r + 1)).erase 0, f j := by
  calc
    _ = ∑ j ∈ Finset.range r, f (j + 1) :=
      Fin.sum_univ_eq_sum_range (fun j => f (j + 1)) r
    _ = _ := by
      refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_range, Finset.mem_erase] at *
        omega
      · intro a ha b hb hab
        omega
      · intro j hj
        simp only [Finset.mem_erase, Finset.mem_range] at hj
        refine ⟨j - 1, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · omega
      · intro j hj
        rfl

/-- Denotation of the literal compiler is exactly the marked incidence argument. -/
theorem denote_compileArgument (β : A) (a : Fin (r + 1) → Fin D → A) :
    SymbolicCost.denote (compileArgument β a) =
      WeightedSupport.incidenceArgument β (semanticRow a 0)
        ((Finset.range (r + 1)).erase 0) (semanticRow a) := by
  have ht :
      (∑ j : Fin r, Polynomial.monomial 0 (Polynomial.monomial (j.val + 1)
        (WeightedSupport.linearForm Finset.univ (a j.succ)))) =
      ∑ j ∈ (Finset.range (r + 1)).erase 0,
        Polynomial.monomial 0 (Polynomial.monomial j (semanticRow a j)) := by
    calc
      _ = ∑ j : Fin r, Polynomial.monomial 0
          (Polynomial.monomial (j.val + 1) (semanticRow a (j.val + 1))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show semanticRow a (j.val + 1) =
          WeightedSupport.linearForm Finset.univ (a j.succ) from semanticRow_fin a j.succ]
      _ = _ := sum_positive (fun j => Polynomial.monomial 0
        (Polynomial.monomial j (semanticRow a j))) r
  have hz : semanticRow a 0 = WeightedSupport.linearForm Finset.univ (a 0) :=
    semanticRow_fin a 0
  simp only [compileArgument, SymbolicCost.denote_append, SymbolicCost.denote,
    monomial_constantIndex, add_zero, denote_rawRow, denote_flatten,
    List.map_ofFn, Function.comp_apply, Fin.sum_ofFn, ht]
  simp only [WeightedSupport.incidenceArgument, WeightedSupport.markedArgument,
    WeightedSupport.scalarHom, RingHom.comp_apply, hz,
    map_neg, sub_eq_add_neg, map_add, Polynomial.monomial_zero_left]
  simp only [add_assoc, add_left_comm, add_comm]

/-- Connect an executable finite Taylor array to the existing row-path argument.
The equality hypothesis only identifies the input scalar array; the literal
compiler itself never reads a mathematical polynomial. -/
theorem denote_compileArgument_eq_rowArgument
    (β θ : A) (a : Fin (r + 1) → Fin D → A) (row : Fin D → Polynomial A)
    (ha : ∀ j i, a j i = ((row i).comp (Polynomial.X + Polynomial.C θ)).coeff j.val) :
    SymbolicCost.denote (compileArgument β a) = Counting.rowArgument row θ β r := by
  have hr : ∀ j, j < r + 1 → semanticRow a j = Counting.rowCoefficient row θ j := by
    intro j hj
    unfold semanticRow Counting.rowCoefficient
    congr 1
    funext i
    simpa [coefficientAt, hj] using ha ⟨j, hj⟩ i
  rw [denote_compileArgument, Counting.rowArgument]
  unfold WeightedSupport.incidenceArgument WeightedSupport.markedArgument
  rw [hr 0 (Nat.succ_pos r)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hr j (Finset.mem_range.mp (Finset.mem_erase.mp hj).2)]

/-- The existing literal-loader bound now applies to this concrete compiler. -/
theorem ingest_compileArgument_cost
    (slots : List (SymbolicCost.RawIndex D))
    (hslots : slots.length = SubexpSymbolicCost.slotCount D)
    (β : A) (a : Fin (r + 1) → Fin D → A) :
    (SubexpSymbolicCost.ingestLiteral slots (compileArgument β a)).2 ≤
      SubexpSymbolicCost.literalFactor D r * SubexpSymbolicCost.monomialCount D :=
  SubexpSymbolicCost.ingestLiteral_cost slots (compileArgument β a) hslots r
    (length_compileArgument_le β a)

theorem ingest_compileArgument_denote
    (slots : List (SymbolicCost.RawIndex D)) (hn : slots.Nodup)
    (hs : ∀ a, a ∈ slots ↔ SymbolicCost.Retained D a)
    (β : A) (a : Fin (r + 1) → Fin D → A) :
    SymbolicCost.denote (SubexpSymbolicCost.ingestLiteral slots (compileArgument β a)).1 =
      Truncation.canonical (D + 1) D (2 * D + 1)
        (WeightedSupport.incidenceArgument β (semanticRow a 0)
          ((Finset.range (r + 1)).erase 0) (semanticRow a)) := by
  rw [SubexpSymbolicCost.ingestLiteral_correct slots hn hs, denote_compileArgument]

end

end Semantics

end SubexponentialSAT.SubexpArgumentCode

end OAI.Algorithms
