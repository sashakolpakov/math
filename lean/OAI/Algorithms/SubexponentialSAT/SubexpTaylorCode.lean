import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentCode
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

namespace OAI.Algorithms

/-!
# Executable Taylor coefficient caches for incidence-argument compilation

Input paths are dense coefficient lists. Each path is shifted once by the
existing Horner loop, then its first q+1 coefficients are read into a real
array cache. Mathematical polynomials occur only in semantic theorems.
-/

namespace SubexponentialSAT.SubexpTaylorCode

open scoped BigOperators

/-- A zero-default coefficient read, charging every visited list cell and
its terminal check. It has the same value as `List.getD`. -/
def readWithCost {A : Type*} [Zero A] : List A → ℕ → A × ℕ
  | [], _ => (0, 1)
  | a :: _, 0 => (a, 1)
  | _ :: P, n + 1 =>
    let rest := readWithCost P n
    (rest.1, rest.2 + 1)

theorem readWithCost_getD {A : Type*} [Zero A] (P : List A) (n : ℕ) :
    (readWithCost P n).1 = P.getD n 0 := by
  induction P generalizing n with
  | nil => simp [readWithCost]
  | cons a P ih => cases n <;> simp [readWithCost, ih ]

theorem readWithCost_le {A : Type*} [Zero A] (P : List A) (n : ℕ) :
    (readWithCost P n).2 ≤ n + 1 := by
  induction P generalizing n with
  | nil => simp [readWithCost]
  | cons a P ih =>
    cases n with
    | zero => simp [readWithCost]
    | succ n => simpa [readWithCost, Nat.add_assoc] using Nat.add_le_add_right (ih n) 1

structure RowCache (A : Type*) where
  values : Array A
  scalarOps : ℕ
  listReads : ℕ

/-- The shifted list is bound once; every lookup result is cached once. -/
def buildRow {A : Type*} [Semiring A] (θ : A) (q : ℕ) (P : List A) : RowCache A :=
  let shifted := PolynomialAlgorithm.shiftWithCost θ P
  let entries := Array.ofFn (fun j : Fin (q + 1) => readWithCost shifted.1 j.val)
  ⟨entries.map Prod.fst, shifted.2, (entries.toList.map Prod.snd).sum⟩

structure TaylorCache (A : Type*) where
  values : Array (Array A)
  scalarOps : ℕ
  listReads : ℕ

/-- Each coordinate's dense path is shifted once before its finite row is
stored. Later consumers read the stored arrays rather than shifting again. -/
def buildTaylor {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → List A) : TaylorCache A :=
  let cached := Array.ofFn (fun i : Fin D => buildRow θ q (rows i))
  ⟨cached.map RowCache.values,
    (cached.toList.map RowCache.scalarOps).sum,
    (cached.toList.map RowCache.listReads).sum⟩

/-- Finite Taylor array in the orientation consumed by `compileArgument`. -/
def coefficients {D q : ℕ} {A : Type*} [Zero A]
    (cache : TaylorCache A) : Fin (q + 1) → Fin D → A :=
  fun j i => (cache.values.getD i.val #[]).getD j.val 0

/-- Direct dense-path-to-raw-incidence compiler. -/
def compileDenseArgument {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q : ℕ) (rows : Fin D → List A) : SymbolicCost.CoeffList D A :=
  let cache := buildTaylor θ q rows
  SubexpArgumentCode.compileArgument β (coefficients (D := D) (q := q) cache)

open SubexpRowInterpolation (PolynomialCode)

/-- Compile the actual finite expression tree to a dense coefficient list.
Recursive outputs are shared with the instrumented arithmetic operations. -/
def compileCodeWithCost {A : Type*} [Semiring A] : PolynomialCode A → List A × ℕ
  | .constant a => ([a], 0)
  | .indeterminate => ([0, 1], 0)
  | .add p q =>
    let left := compileCodeWithCost p
    let right := compileCodeWithCost q
    let result := PolynomialAlgorithm.addWithCost left.1 right.1
    (result.1, left.2 + right.2 + result.2)
  | .mul p q =>
    let left := compileCodeWithCost p
    let right := compileCodeWithCost q
    let result := PolynomialAlgorithm.mulWithCost left.1 right.1
    (result.1, left.2 + right.2 + result.2)

/-- A scalar-independent size of the finite expression; X receives weight two
because its dense list stores both its constant and linear coefficient. -/
def codeWeight {A : Type*} : PolynomialCode A → ℕ
  | .constant _ => 1
  | .indeterminate => 2
  | .add p q | .mul p q => codeWeight p + codeWeight q + 1

/-- A sharper bound for stored list length: addition takes a maximum. -/
def codeLengthBound {A : Type*} : PolynomialCode A → ℕ
  | .constant _ => 1
  | .indeterminate => 2
  | .add p q => max (codeLengthBound p) (codeLengthBound q)
  | .mul p q => codeLengthBound p + codeLengthBound q

theorem compileCode_lengthBound {A : Type*} [Semiring A] (p : PolynomialCode A) :
    (compileCodeWithCost p).1.length ≤ codeLengthBound p := by
  induction p with
  | constant a => rfl
  | indeterminate => rfl
  | add p q hp hq =>
    exact (PolynomialAlgorithm.addWithCost_length _ _).le.trans (max_le_max hp hq)
  | mul p q hp hq =>
    exact (PolynomialAlgorithm.mulWithCost_length_le _ _).trans (Nat.add_le_add hp hq)

theorem codeLengthBound_le_weight {A : Type*} (p : PolynomialCode A) :
    codeLengthBound p ≤ codeWeight p := by
  induction p with
  | constant a => rfl
  | indeterminate => rfl
  | add p q hp hq => simp only [codeLengthBound, codeWeight]; omega
  | mul p q hp hq => simp only [codeLengthBound, codeWeight]; omega

theorem compileCode_length {A : Type*} [Semiring A] (p : PolynomialCode A) :
    (compileCodeWithCost p).1.length ≤ codeWeight p :=
  (compileCode_lengthBound p).trans (codeLengthBound_le_weight p)

theorem compileCode_cost {A : Type*} [Semiring A] (p : PolynomialCode A) :
    (compileCodeWithCost p).2 ≤ 2 * codeWeight p ^ 2 := by
  induction p with
  | constant a => simp [compileCodeWithCost, codeWeight]
  | indeterminate => simp [compileCodeWithCost, codeWeight]
  | add p q hp hq =>
    have hlen := compileCode_length p
    have hmin := Nat.min_le_left (compileCodeWithCost p).1.length
      (compileCodeWithCost q).1.length
    simp only [compileCodeWithCost, codeWeight, PolynomialAlgorithm.addWithCost_cost]
    nlinarith [Nat.zero_le (codeWeight p * codeWeight q)]
  | mul p q hp hq =>
    have hmul := (PolynomialAlgorithm.mulWithCost_cost_le
      (compileCodeWithCost p).1 (compileCodeWithCost q).1).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (compileCode_length p)) (compileCode_length q))
    simp only [compileCodeWithCost, codeWeight]
    nlinarith [Nat.zero_le (codeWeight p * codeWeight q)]

structure CompiledTaylorCache (A : Type*) where
  taylor : TaylorCache A
  compileOps : ℕ

/-- Compile every coordinate once, then shift and cache its coefficients once.
The compiled lists are stored before either their values or costs are read. -/
def buildCodeTaylor {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → PolynomialCode A) : CompiledTaylorCache A :=
  let compiled := Array.ofFn (fun i : Fin D => compileCodeWithCost (rows i))
  ⟨buildTaylor θ q (fun i : Fin D => (compiled.getD i.val ([], 0)).1),
    (compiled.toList.map Prod.snd).sum⟩

/-- Complete expression-path-to-raw-incidence compiler. -/
def compileCodeArgument {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q : ℕ) (rows : Fin D → PolynomialCode A) : SymbolicCost.CoeffList D A :=
  let cache := buildCodeTaylor θ q rows
  SubexpArgumentCode.compileArgument β (coefficients (D := D) (q := q) cache.taylor)

/-- Costs remain in their declared units: coefficient-ring arithmetic,
coefficient-list visits, and raw-emitter construction events. -/
structure ArgumentResult (D : ℕ) (A : Type*) where
  raw : SymbolicCost.CoeffList D A
  compileOps : ℕ
  shiftOps : ℕ
  listReads : ℕ
  emitEvents : ℕ

/-- Instrumented complete frontend, sharing both the cache and raw emitter. -/
def compileCodeArgumentWithCost {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q : ℕ) (rows : Fin D → PolynomialCode A) : ArgumentResult D A :=
  let cache := buildCodeTaylor θ q rows
  let emitted := SubexpArgumentCode.compileArgumentWithCost β
    (coefficients (D := D) (q := q) cache.taylor)
  ⟨emitted.1, cache.compileOps, cache.taylor.scalarOps, cache.taylor.listReads, emitted.2⟩

@[simp] theorem compileCodeArgumentWithCost_raw {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q : ℕ) (rows : Fin D → PolynomialCode A) :
    (compileCodeArgumentWithCost θ β q rows).raw = compileCodeArgument θ β q rows := by
  simp only [compileCodeArgumentWithCost, SubexpArgumentCode.compileArgumentWithCost_eq]
  rfl

@[simp] theorem compileCodeArgumentWithCost_emitEvents {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q : ℕ) (rows : Fin D → PolynomialCode A) :
    (compileCodeArgumentWithCost θ β q rows).emitEvents = 4 * (q + 1) * D + q + 3 := by
  simp only [compileCodeArgumentWithCost, SubexpArgumentCode.compileArgumentWithCost_eq]

@[simp] theorem length_compileDenseArgument {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q : ℕ) (rows : Fin D → List A) :
    (compileDenseArgument θ β q rows).length = 2 + (q + 1) * D :=
  SubexpArgumentCode.length_compileArgument β _

@[simp] theorem length_compileCodeArgument {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q : ℕ) (rows : Fin D → PolynomialCode A) :
    (compileCodeArgument θ β q rows).length = 2 + (q + 1) * D :=
  SubexpArgumentCode.length_compileArgument β _

@[simp] theorem getD_ofFn {B : Type*} {n : ℕ}
    (f : Fin n → B) (i : Fin n) (fallback : B) :
    (Array.ofFn f).getD i.val fallback = f i := by
  simp [Array.getD, i.isLt]

@[simp] theorem getD_map_ofFn {B C : Type*} {n : ℕ}
    (f : Fin n → B) (g : B → C) (i : Fin n) (fallback : C) :
    ((Array.ofFn f).map g).getD i.val fallback = g (f i) := by
  simp [Array.getD, i.isLt]

@[simp] theorem buildRow_size {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (P : List A) : (buildRow θ q P).values.size = q + 1 := by
  simp [buildRow]

@[simp] theorem buildTaylor_size {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → List A) :
    (buildTaylor θ q rows).values.size = D := by
  simp [buildTaylor]

@[simp] theorem buildTaylor_row {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → List A) (i : Fin D) :
    (buildTaylor θ q rows).values.getD i.val #[] = (buildRow θ q (rows i)).values := by
  exact getD_map_ofFn _ _ i #[]

@[simp] theorem buildTaylor_row_size {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → List A) (i : Fin D) :
    ((buildTaylor θ q rows).values.getD i.val #[]).size = q + 1 := by
  rw [buildTaylor_row, buildRow_size]

@[simp] theorem buildRow_getD {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (P : List A) (j : Fin (q + 1)) :
    (buildRow θ q P).values.getD j.val 0 =
      (PolynomialAlgorithm.shiftWithCost θ P).1.getD j.val 0 := by
  rw [buildRow]
  rw [getD_map_ofFn]
  exact readWithCost_getD _ _

theorem buildRow_scalarOps {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (P : List A) :
    (buildRow θ q P).scalarOps ≤ 5 * P.length ^ 2 :=
  PolynomialAlgorithm.shiftWithCost_cost_le θ P

theorem buildRow_listReads {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (P : List A) :
    (buildRow θ q P).listReads ≤ (q + 1) ^ 2 := by
  change ((Array.ofFn (fun j : Fin (q + 1) =>
    readWithCost (PolynomialAlgorithm.shiftWithCost θ P).1 j.val)).toList.map Prod.snd).sum ≤ _
  simp only [Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _j : Fin (q + 1), (q + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (readWithCost_le _ j.val).trans (by omega)
    _ = _ := by simp [pow_two]

theorem buildTaylor_scalarOps {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q L : ℕ) (rows : Fin D → List A) (hL : ∀ i, (rows i).length ≤ L) :
    (buildTaylor θ q rows).scalarOps ≤ 5 * D * L ^ 2 := by
  simp only [buildTaylor, Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin D, 5 * L ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (buildRow_scalarOps θ q (rows i)).trans
        (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (hL i) 2))
    _ = _ := by simp; ring

theorem buildTaylor_listReads {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → List A) :
    (buildTaylor θ q rows).listReads ≤ D * (q + 1) ^ 2 := by
  simp only [buildTaylor, Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin D, (q + 1) ^ 2 :=
      Finset.sum_le_sum (fun i _ => buildRow_listReads θ q (rows i))
    _ = _ := by simp

@[simp] theorem buildCodeTaylor_taylor {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → PolynomialCode A) :
    (buildCodeTaylor θ q rows).taylor =
      buildTaylor θ q (fun i => (compileCodeWithCost (rows i)).1) := by
  simp only [buildCodeTaylor, getD_ofFn]

theorem buildCodeTaylor_compileOps {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q W : ℕ) (rows : Fin D → PolynomialCode A)
    (hW : ∀ i, codeWeight (rows i) ≤ W) :
    (buildCodeTaylor θ q rows).compileOps ≤ 2 * D * W ^ 2 := by
  simp only [buildCodeTaylor, Array.toList_ofFn, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin D, 2 * W ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (compileCode_cost (rows i)).trans
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hW i) 2))
    _ = _ := by simp; ring

theorem buildCodeTaylor_scalarOps {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q L : ℕ) (rows : Fin D → PolynomialCode A)
    (hL : ∀ i, codeLengthBound (rows i) ≤ L) :
    (buildCodeTaylor θ q rows).taylor.scalarOps ≤ 5 * D * L ^ 2 := by
  rw [buildCodeTaylor_taylor]
  exact buildTaylor_scalarOps θ q L _ (fun i => (compileCode_lengthBound (rows i)).trans (hL i))

theorem buildCodeTaylor_listReads {D : ℕ} {A : Type*} [Semiring A]
    (θ : A) (q : ℕ) (rows : Fin D → PolynomialCode A) :
    (buildCodeTaylor θ q rows).taylor.listReads ≤ D * (q + 1) ^ 2 := by
  rw [buildCodeTaylor_taylor]
  exact buildTaylor_listReads θ q _

theorem compileCodeArgumentWithCost_bounds {D : ℕ} {A : Type*} [Ring A]
    (θ β : A) (q W L : ℕ) (rows : Fin D → PolynomialCode A)
    (hW : ∀ i, codeWeight (rows i) ≤ W) (hL : ∀ i, codeLengthBound (rows i) ≤ L) :
    (compileCodeArgumentWithCost θ β q rows).compileOps ≤ 2 * D * W ^ 2 ∧
    (compileCodeArgumentWithCost θ β q rows).shiftOps ≤ 5 * D * L ^ 2 ∧
    (compileCodeArgumentWithCost θ β q rows).listReads ≤ D * (q + 1) ^ 2 ∧
    (compileCodeArgumentWithCost θ β q rows).emitEvents = 4 * (q + 1) * D + q + 3 :=
  ⟨buildCodeTaylor_compileOps θ q W rows hW,
    buildCodeTaylor_scalarOps θ q L rows hL,
    buildCodeTaylor_listReads θ q rows,
    compileCodeArgumentWithCost_emitEvents θ β q rows⟩

section Semantics

noncomputable section

variable {A : Type*} [CommRing A]

theorem codeLengthBound_sum (ps : List (PolynomialCode A)) (L : ℕ) (hL : 1 ≤ L)
    (h : ∀ p ∈ ps, codeLengthBound p ≤ L) :
    codeLengthBound (PolynomialCode.sum ps) ≤ L := by
  induction ps with
  | nil => exact hL
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem codeLengthBound_product (ps : List (PolynomialCode A)) (L : ℕ)
    (h : ∀ p ∈ ps, codeLengthBound p ≤ L) :
    codeLengthBound (PolynomialCode.product ps) ≤ ps.length * L + 1 := by
  induction ps with
  | nil => simp [PolynomialCode.product, codeLengthBound]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    change codeLengthBound p + codeLengthBound (PolynomialCode.product ps) ≤ _
    simp only [List.length_cons]
    nlinarith

theorem codeWeight_sum (ps : List (PolynomialCode A)) (W : ℕ)
    (h : ∀ p ∈ ps, codeWeight p ≤ W) :
    codeWeight (PolynomialCode.sum ps) ≤ ps.length * (W + 1) + 1 := by
  induction ps with
  | nil => simp [PolynomialCode.sum, codeWeight]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    change codeWeight p + codeWeight (PolynomialCode.sum ps) + 1 ≤ _
    simp only [List.length_cons]
    nlinarith

theorem codeWeight_product (ps : List (PolynomialCode A)) (W : ℕ)
    (h : ∀ p ∈ ps, codeWeight p ≤ W) :
    codeWeight (PolynomialCode.product ps) ≤ ps.length * (W + 1) + 1 := by
  induction ps with
  | nil => simp [PolynomialCode.product, codeWeight]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    change codeWeight p + codeWeight (PolynomialCode.product ps) + 1 ≤ _
    simp only [List.length_cons]
    nlinarith

section InterpolationBounds

open SubexpRowInterpolation

variable {Q : ℕ} {node : Fin Q → A}

theorem basisCode_lengthBound (u : NodeUnits node) (s : Finset (Fin Q)) (i : Fin Q) :
    codeLengthBound (basisCode u s i) ≤ 3 * Q + 4 := by
  unfold basisCode
  have h := codeLengthBound_product (List.ofFn (fun j : Fin Q =>
    if j ∈ s.erase i then
      PolynomialCode.mul (.constant (u.differenceInverse i j))
        (.add .indeterminate (.constant (-node j)))
    else .constant 1)) 3 (by
      intro p hp
      rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩
      split_ifs <;> norm_num [codeLengthBound])
  simp only [List.length_ofFn] at h
  change 1 + 2 + _ ≤ _
  omega

theorem basisCode_weight (u : NodeUnits node) (s : Finset (Fin Q)) (i : Fin Q) :
    codeWeight (basisCode u s i) ≤ 7 * Q + 6 := by
  unfold basisCode
  have h := codeWeight_product (List.ofFn (fun j : Fin Q =>
    if j ∈ s.erase i then
      PolynomialCode.mul (.constant (u.differenceInverse i j))
        (.add .indeterminate (.constant (-node j)))
    else .constant 1)) 6 (by
      intro p hp
      rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩
      split_ifs <;> norm_num [codeWeight])
  simp only [List.length_ofFn] at h
  change (1 + 2 + 1) + _ + 1 ≤ _
  omega

theorem correctionCode_lengthBound (u : NodeUnits node) (s : Finset (Fin Q))
    (d : Fin Q → A) : codeLengthBound (correctionCode u s d) ≤ 3 * Q + 5 := by
  apply codeLengthBound_sum _ _ (by omega)
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  split_ifs
  · change 1 + codeLengthBound (basisCode u s i) ≤ _
    have h := basisCode_lengthBound u s i
    omega
  · simp [codeLengthBound]

theorem correctionCode_weight (u : NodeUnits node) (s : Finset (Fin Q))
    (d : Fin Q → A) : codeWeight (correctionCode u s d) ≤ Q * (7 * Q + 9) + 1 := by
  have h := codeWeight_sum (List.ofFn (fun i : Fin Q =>
    if i ∈ s then PolynomialCode.mul (.constant (d i)) (basisCode u s i)
    else .constant 0)) (7 * Q + 8) (by
      intro p hp
      rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
      split_ifs
      · change 1 + codeWeight (basisCode u s i) + 1 ≤ _
        have hb := basisCode_weight u s i
        omega
      · simp [codeWeight])
  simpa only [List.length_ofFn, correctionCode, Nat.add_assoc] using h

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

theorem mismatchRowCode_lengthBound (v : V) (head : V → Fin Q → C) (σ : Fin Q → C)
    (r : ℕ) (u : NodeUnits node) (d : V → Fin Q → A) (y : V) :
    codeLengthBound (mismatchRowCode v head σ r u d y) ≤ 3 * Q + 5 := by
  unfold mismatchRowCode
  simp only [codeLengthBound]
  apply max_le (by omega)
  split_ifs
  · exact correctionCode_lengthBound u _ _
  · simp [codeLengthBound]

theorem mismatchRowCode_weight (v : V) (head : V → Fin Q → C) (σ : Fin Q → C)
    (r : ℕ) (u : NodeUnits node) (d : V → Fin Q → A) (y : V) :
    codeWeight (mismatchRowCode v head σ r u d y) ≤ Q * (7 * Q + 9) + 3 := by
  unfold mismatchRowCode
  simp only [codeWeight]
  split_ifs
  · have h := correctionCode_weight u (mismatchPositions head σ y) (d y)
    omega
  · simp [codeWeight]

/-- Dense output length for the actual row-expression constructor, including
any trailing zero padding introduced by the schoolbook arithmetic. -/
theorem compile_mismatchRowCode_length (v : V) (head : V → Fin Q → C) (σ : Fin Q → C)
    (r : ℕ) (u : NodeUnits node) (d : V → Fin Q → A) (y : V) :
    (compileCodeWithCost (mismatchRowCode v head σ r u d y)).1.length ≤ 3 * Q + 5 :=
  (compileCode_lengthBound _).trans (mismatchRowCode_lengthBound v head σ r u d y)

theorem compile_mismatchRowCode_cost (v : V) (head : V → Fin Q → C) (σ : Fin Q → C)
    (r : ℕ) (u : NodeUnits node) (d : V → Fin Q → A) (y : V) :
    (compileCodeWithCost (mismatchRowCode v head σ r u d y)).2 ≤
      2 * (Q * (7 * Q + 9) + 3) ^ 2 :=
  (compileCode_cost _).trans (Nat.mul_le_mul_left 2
    (Nat.pow_le_pow_left (mismatchRowCode_weight v head σ r u d y) 2))

theorem compile_mismatchArgument_bounds {D : ℕ} (θ β : A) (q : ℕ)
    (v : Fin D) (head : Fin D → Fin Q → C) (σ : Fin Q → C)
    (r : ℕ) (u : NodeUnits node) (d : Fin D → Fin Q → A) :
    let result := compileCodeArgumentWithCost θ β q (mismatchRowCode v head σ r u d)
    result.compileOps ≤ 2 * D * (Q * (7 * Q + 9) + 3) ^ 2 ∧
    result.shiftOps ≤ 5 * D * (3 * Q + 5) ^ 2 ∧
    result.listReads ≤ D * (q + 1) ^ 2 ∧
    result.emitEvents = 4 * (q + 1) * D + q + 3 :=
  compileCodeArgumentWithCost_bounds θ β q _ _ _
    (mismatchRowCode_weight v head σ r u d)
    (mismatchRowCode_lengthBound v head σ r u d)

end InterpolationBounds

@[simp] theorem denote_compileCodeWithCost (p : PolynomialCode A) :
    PolynomialAlgorithm.denote (compileCodeWithCost p).1 = p.denote := by
  induction p with
  | constant a => simp [compileCodeWithCost, PolynomialAlgorithm.denote, PolynomialCode.denote]
  | indeterminate => simp [compileCodeWithCost, PolynomialAlgorithm.denote, PolynomialCode.denote]
  | add p q hp hq => simp [compileCodeWithCost, PolynomialCode.denote, hp, hq]
  | mul p q hp hq => simp [compileCodeWithCost, PolynomialCode.denote, hp, hq]

theorem readWithCost_coeff (P : List A) (n : ℕ) :
    (readWithCost P n).1 = (PolynomialAlgorithm.denote P).coeff n := by
  rw [PolynomialAlgorithm.coeff_denote]
  induction P generalizing n with
  | nil => rfl
  | cons a P ih => cases n <;> simp [readWithCost, PolynomialAlgorithm.coeff, ih]

theorem buildRow_coeff (θ : A) (q : ℕ) (P : List A) (j : Fin (q + 1)) :
    (buildRow θ q P).values.getD j.val 0 =
      ((PolynomialAlgorithm.denote P).comp (Polynomial.X + Polynomial.C θ)).coeff j.val := by
  rw [buildRow_getD, ← readWithCost_getD, readWithCost_coeff,
    PolynomialAlgorithm.denote_shiftWithCost]

/-- Every stored scalar is the coefficient of the actual shifted polynomial. -/
theorem coefficients_buildTaylor {D : ℕ} (θ : A) (q : ℕ)
    (rows : Fin D → List A) (j : Fin (q + 1)) (i : Fin D) :
    coefficients (buildTaylor θ q rows) j i =
      ((PolynomialAlgorithm.denote (rows i)).comp (Polynomial.X + Polynomial.C θ)).coeff j.val := by
  unfold coefficients
  rw [buildTaylor_row]
  exact buildRow_coeff θ q (rows i) j

theorem denote_compileDenseArgument {D : ℕ} (θ β : A) (q : ℕ)
    (rows : Fin D → List A) :
    SymbolicCost.denote (compileDenseArgument θ β q rows) =
      Counting.rowArgument (fun i => PolynomialAlgorithm.denote (rows i)) θ β q := by
  apply SubexpArgumentCode.denote_compileArgument_eq_rowArgument
  intro j i
  exact coefficients_buildTaylor θ q rows j i

theorem coefficients_buildCodeTaylor {D : ℕ} (θ : A) (q : ℕ)
    (rows : Fin D → PolynomialCode A) (j : Fin (q + 1)) (i : Fin D) :
    coefficients (buildCodeTaylor θ q rows).taylor j i =
      ((rows i).denote.comp (Polynomial.X + Polynomial.C θ)).coeff j.val := by
  rw [buildCodeTaylor_taylor, coefficients_buildTaylor, denote_compileCodeWithCost]

theorem denote_compileCodeArgument {D : ℕ} (θ β : A) (q : ℕ)
    (rows : Fin D → PolynomialCode A) :
    SymbolicCost.denote (compileCodeArgument θ β q rows) =
      Counting.rowArgument (fun i => (rows i).denote) θ β q := by
  apply SubexpArgumentCode.denote_compileArgument_eq_rowArgument
  intro j i
  exact coefficients_buildCodeTaylor θ q rows j i

theorem denote_compileCodeArgumentWithCost {D : ℕ} (θ β : A) (q : ℕ)
    (rows : Fin D → PolynomialCode A) :
    SymbolicCost.denote (compileCodeArgumentWithCost θ β q rows).raw =
      Counting.rowArgument (fun i => (rows i).denote) θ β q := by
  rw [compileCodeArgumentWithCost_raw, denote_compileCodeArgument]

/-- End-to-end specialization to the generated interpolation expressions. -/
theorem denote_compile_mismatchArgument {D Q : ℕ} {C : Type*} [DecidableEq C]
    {node : Fin Q → A} (θ β : A) (q : ℕ) (v : Fin D)
    (head : Fin D → Fin Q → C) (σ : Fin Q → C) (r : ℕ)
    (u : SubexpRowInterpolation.NodeUnits node) (d : Fin D → Fin Q → A) :
    SymbolicCost.denote (compileCodeArgument θ β q
      (SubexpRowInterpolation.mismatchRowCode v head σ r u d)) =
      Counting.rowArgument (SubexpRowInterpolation.mismatchRowPath v head σ r u d) θ β q := by
  rw [denote_compileCodeArgument]
  congr 1
  funext i
  exact SubexpRowInterpolation.mismatchRowCode_denote v head σ r u d i

end

end Semantics

end SubexponentialSAT.SubexpTaylorCode

end OAI.Algorithms
