import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SymbolicCost
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic

namespace OAI.Algorithms

/-!
# Uniform symbolic list costs for growing parameters

The old canonical-list algorithm has an explicit fixed-degree event bound. This
module retains its interfaces and makes all parameter dependence visible. It also
refines exponent addition to an actual unary bit-string algorithm. Unary is used
only for exponent indices, whose values are O(D), never for ring coefficients.

Counters below are charged operations/bit inspections. A primitive tape-machine
execution certificate is a separate requirement.
-/

namespace SubexponentialSAT.SubexpSymbolicCost

open SubexponentialSAT.SymbolicCost

/-- Ring coefficients have h base-ring coordinates, each with at most (D+1)b bits.
Here b is a supplied upper bound on log₂ p; no fixed-parameter constant is hidden. -/
def coefficientBits (D h b : ℕ) : ℕ := h * (D + 1) * b

def indexBits (D : ℕ) : ℕ := (D + 2) * (2 * D + 2)

def slotBits (D h b : ℕ) : ℕ := indexBits D + coefficientBits D h b

def monomialCount (D : ℕ) : ℕ :=
  (3 * D + 1).choose D

def slotCount (D : ℕ) : ℕ := monomialCount D * ((D + 1) * D)

/-- Exact fixed-degree polynomial multiplier of M_X^4 in the actual old
instrumented list algorithm. It does not depend on k, p, or h. -/
def listFactor (D : ℕ) : ℕ := 10 * (D * (D + 1) + 1) ^ 3

/-- A single size variable for displaying absolute polynomial degrees. -/
def parameterSize (D h b : ℕ) : ℕ := D + h + b + 2

theorem listFactor_degree (D h b : ℕ) :
    listFactor D ≤ 10 * parameterSize D h b ^ 6 := by
  let S := parameterSize D h b
  have hD : D + 1 ≤ S := by dsimp [S, parameterSize]; omega
  have hbase : D * (D + 1) + 1 ≤ (D + 1) ^ 2 := by
    have he : (D + 1) ^ 2 = D * (D + 1) + 1 + D := by ring
    omega
  have hb : D * (D + 1) + 1 ≤ S ^ 2 :=
    hbase.trans (Nat.pow_le_pow_left hD 2)
  calc
    listFactor D ≤ 10 * (S ^ 2) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 3)
    _ = 10 * S ^ 6 := by ring

theorem indexBits_degree (D h b : ℕ) :
    indexBits D ≤ 2 * parameterSize D h b ^ 2 := by
  let S := parameterSize D h b
  have h₁ : D + 2 ≤ S := by dsimp [S, parameterSize]; omega
  have h₂ : 2 * D + 2 ≤ 2 * S := by dsimp [S, parameterSize]; omega
  calc
    indexBits D ≤ S * (2 * S) := Nat.mul_le_mul h₁ h₂
    _ = 2 * S ^ 2 := by ring

theorem coefficientBits_degree (D h b : ℕ) :
    coefficientBits D h b ≤ parameterSize D h b ^ 3 := by
  let S := parameterSize D h b
  have hD : D + 1 ≤ S := by dsimp [S, parameterSize]; omega
  have hh : h ≤ S := by dsimp [S, parameterSize]; omega
  have hb : b ≤ S := by dsimp [S, parameterSize]; omega
  calc
    coefficientBits D h b ≤ (S * S) * S :=
      Nat.mul_le_mul (Nat.mul_le_mul hh hD) hb
    _ = S ^ 3 := by ring

theorem slotBits_degree (D h b : ℕ) :
    slotBits D h b ≤ 3 * parameterSize D h b ^ 3 := by
  have hi := indexBits_degree D h b
  have hc := coefficientBits_degree D h b
  have hS : 1 ≤ parameterSize D h b := by unfold parameterSize; omega
  have hp : parameterSize D h b ^ 2 ≤ parameterSize D h b ^ 3 :=
    Nat.pow_le_pow_right hS (by decide)
  unfold slotBits
  omega

theorem dense_events_uniform (D : ℕ) :
    denseCost (slotCount D) ≤ listFactor D * monomialCount D ^ 4 := by
  simpa [slotCount, monomialCount, listFactor, symbolicFactor,
    SubexponentialSAT.MonomialCount.card_retainedMonomial, SubexponentialSAT.MonomialCount.card_retainedX]
    using denseCost_retained_le D

theorem dense_add_events_uniform (D : ℕ) :
    denseAddCost (slotCount D) ≤ listFactor D * monomialCount D ^ 4 := by
  simpa [slotCount, monomialCount, listFactor, symbolicFactor,
    SubexponentialSAT.MonomialCount.card_retainedMonomial, SubexponentialSAT.MonomialCount.card_retainedX]
    using denseAddCost_retained_le D

/-- Uniform input/output key size; coefficients are not encoded in unary. -/
theorem retained_index_bits {D : ℕ} (a : RawIndex D) (ha : Retained D a) :
    (encodeIndex a).length ≤ indexBits D := encodeIndex_length_le a ha

/-- The weight q is an independently verified per-event realization bound.
This arithmetic consequence alone is not a machine-runtime theorem. -/
theorem weighted_dense_events_uniform (D q : ℕ) :
    q * denseCost (slotCount D) ≤ (q * listFactor D) * monomialCount D ^ 4 := by
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left q (dense_events_uniform D)

/-- Absolute degree accounting once an independently realized event cost has
been bounded. This does not manufacture that realization certificate. -/
theorem weighted_dense_events_degree (D h b q c degree : ℕ)
    (hq : q ≤ c * parameterSize D h b ^ degree) :
    q * denseCost (slotCount D) ≤
      (10 * c * parameterSize D h b ^ (degree + 6)) * monomialCount D ^ 4 := by
  apply (weighted_dense_events_uniform D q).trans
  have hm : q * listFactor D ≤
      10 * c * parameterSize D h b ^ (degree + 6) := by
    calc
      q * listFactor D ≤ (c * parameterSize D h b ^ degree) *
          (10 * parameterSize D h b ^ 6) := Nat.mul_le_mul hq (listFactor_degree D h b)
      _ = 10 * c * parameterSize D h b ^ (degree + 6) := by rw [pow_add]; ring
  exact Nat.mul_le_mul_right _ hm

/-- Add two unary-delimited sequences directly, copying true bits from each
current number, then consuming both false delimiters. Each transition inspects
at most two bits and writes at most one bit; the counter charges three events. -/
def addIndexBits : List Bool → List Bool → List Bool × ℕ
  | true :: xs, ys =>
    let rest := addIndexBits xs ys
    (true :: rest.1, rest.2 + 3)
  | false :: xs, true :: ys =>
    let rest := addIndexBits (false :: xs) ys
    (true :: rest.1, rest.2 + 3)
  | false :: xs, false :: ys =>
    let rest := addIndexBits xs ys
    (false :: rest.1, rest.2 + 3)
  | _, _ => ([], 1)
termination_by xs ys => xs.length + ys.length

/-- The two current unary numbers are added without converting them to Nat. -/
theorem addIndexBits_prefix (n m : ℕ) (xs ys : List Bool) :
    addIndexBits (unaryWord n ++ xs) (unaryWord m ++ ys) =
      (unaryWord (n + m) ++ (addIndexBits xs ys).1,
        (addIndexBits xs ys).2 + 3 * (n + m + 1)) := by
  induction n with
  | zero =>
    induction m with
    | zero => simp [unaryWord, addIndexBits]
    | succ m ih =>
      simp only [unaryWord, List.replicate_succ, List.replicate_zero,
        List.nil_append, List.cons_append, Nat.zero_add] at *
      simp only [addIndexBits]
      rw [ih]
      simp only [ ]
      congr 1
  | succ n ih =>
    simp only [unaryWord, List.replicate_succ, List.cons_append,
      Nat.succ_add] at *
    simp only [addIndexBits]
    rw [ih]
    simp only [ ]
    congr 1

/-- Correctness for equal-length coordinate arrays. -/
theorem addIndexBits_words (as bs : List ℕ) (hlen : as.length = bs.length) :
    (addIndexBits (unaryWords as) (unaryWords bs)).1 =
      unaryWords (List.zipWith (· + ·) as bs) := by
  induction as generalizing bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst bs
    simp [unaryWords, addIndexBits]
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have ht : as.length = bs.length := Nat.succ.inj hlen
      change (addIndexBits (unaryWord a ++ unaryWords as)
        (unaryWord b ++ unaryWords bs)).1 =
          unaryWord (a + b) ++ unaryWords (List.zipWith (· + ·) as bs)
      rw [addIndexBits_prefix]
      simp only [ ih bs ht]

/-- Every recursive call consumes at least one actual input bit. -/
theorem addIndexBits_cost (xs ys : List Bool) :
    (addIndexBits xs ys).2 ≤ 3 * (xs.length + ys.length) + 1 := by
  fun_induction addIndexBits xs ys
  all_goals simp_all (config := { zetaDelta := true }) only [List.length_cons]
  all_goals omega

theorem zipWith_ofFn_add {D : ℕ} (a b : Fin D → ℕ) :
    List.zipWith (· + ·) (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

theorem indexData_add {D : ℕ} (a b : RawIndex D) :
    indexData (a + b) = List.zipWith (· + ·) (indexData a) (indexData b) := by
  simp only [indexData]
  rw [List.zipWith_append (by simp), zipWith_ofFn_add]
  rfl

theorem addIndexBits_correct {D : ℕ} (a b : RawIndex D) :
    (addIndexBits (encodeIndex a) (encodeIndex b)).1 = encodeIndex (a + b) := by
  rw [encodeIndex, encodeIndex, addIndexBits_words _ _ (by simp), ← indexData_add]
  rfl

theorem addIndexBits_retained_cost {D : ℕ} (a b : RawIndex D)
    (ha : Retained D a) (hb : Retained D b) :
    (addIndexBits (encodeIndex a) (encodeIndex b)).2 ≤ 6 * indexBits D + 1 := by
  apply (addIndexBits_cost _ _).trans
  have h := Nat.add_le_add (retained_index_bits a ha) (retained_index_bits b hb)
  omega

section FramedKeys

theorem unaryWords_append (xs ys : List ℕ) :
    unaryWords (xs ++ ys) = unaryWords xs ++ unaryWords ys := by
  simp [unaryWords]

theorem unaryWords_zeroes (n : ℕ) :
    unaryWords (List.replicate n 0) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false :: unaryWords (List.replicate n 0) = false :: List.replicate n false
    rw [ih]

/-- Fixed-width framing for record scans. Padding is outside the D+2 unary
numbers, so reading exactly those D+2 numbers recovers the original key. -/
def fixedKey {D : ℕ} (a : RawIndex D) : List Bool :=
  encodeIndex a ++ List.replicate (indexBits D - (encodeIndex a).length) false

theorem fixedKey_decode {D : ℕ} (a : RawIndex D) :
    (decodeUnary (fixedKey a) 0).take (D + 2) = indexData a := by
  have he : fixedKey a = unaryWords (indexData a ++
      List.replicate (indexBits D - (encodeIndex a).length) 0) := by
    rw [unaryWords_append, unaryWords_zeroes]
    rfl
  rw [he, decodeUnary_words]
  exact List.take_left' (length_indexData a)

theorem fixedKey_injective {D : ℕ} : Function.Injective (@fixedKey D) := by
  intro a b h
  have hd := congrArg (fun bits => (decodeUnary bits 0).take (D + 2)) h
  rw [fixedKey_decode, fixedKey_decode] at hd
  exact indexData_injective hd

theorem fixedKey_length {D : ℕ} (a : RawIndex D) (ha : Retained D a) :
    (fixedKey a).length = indexBits D := by
  simp only [fixedKey, List.length_append, List.length_replicate]
  exact Nat.add_sub_of_le (retained_index_bits a ha)

abbrev RetainedKey (D : ℕ) := {a : RawIndex D // Retained D a}

/-- A computable fixed-width record key, ready for BitProgram scans. -/
def keyBlockCode (D : ℕ) : SubexponentialSAT.StackEncoding.BlockCode (RetainedKey D) where
  width := indexBits D
  width_pos := Nat.mul_pos (by omega) (by omega)
  block a := fixedKey a.1
  length_block a := fixedKey_length a.1 a.2
  injective_block := fun a b h => Subtype.ext (fixedKey_injective h)

/-- Fixed-width key/payload records, with the key at the head of the stream. -/
def recordBlockCode {K C : Type*} (key : SubexponentialSAT.StackEncoding.BlockCode K)
    (payload : SubexponentialSAT.StackEncoding.BlockCode C) : SubexponentialSAT.StackEncoding.BlockCode (K × C) where
  width := key.width + payload.width
  width_pos := Nat.add_pos_left key.width_pos _
  block p := key.block p.1 ++ payload.block p.2
  length_block p := by simp [key.length_block, payload.length_block]
  injective_block := by
    intro a b h
    have hk := congrArg (List.take key.width) h
    have hp := congrArg (List.drop key.width) h
    simp only [SubexponentialSAT.StackEncoding.take_block_append] at hk
    simp only [SubexponentialSAT.StackEncoding.drop_block_append] at hp
    exact Prod.ext (key.injective_block hk) (payload.injective_block hp)

end FramedKeys

section FramedRecords

/-- Escape framing makes record boundaries explicit to finite-control scans. -/
def framedRecord (key payload : List Bool) : List Bool :=
  SubexponentialSAT.Encoding.frame key ++ SubexponentialSAT.Encoding.frame payload

theorem framedRecord_length (key payload : List Bool) :
    (framedRecord key payload).length = 2 * key.length + 2 * payload.length + 2 := by
  simp only [framedRecord, List.length_append, SubexponentialSAT.Encoding.length_frame]
  omega

theorem framedRecord_read_key (key payload tail : List Bool) :
    SubexponentialSAT.Encoding.readFrame (framedRecord key payload ++ tail) =
      some (key, SubexponentialSAT.Encoding.frame payload ++ tail) := by
  simp [framedRecord, List.append_assoc]

theorem framedRecord_injective :
    Function.Injective (fun p : List Bool × List Bool => framedRecord p.1 p.2) := by
  intro a b h
  have hk := SubexponentialSAT.Encoding.frame_append_injective h
  have hp := SubexponentialSAT.Encoding.frame_append_injective
    (bits := a.2) (bits' := b.2) (rest := []) (rest' := []) (by simpa using hk.2)
  exact Prod.ext hk.1 hp.1

theorem framedCoefficient_length {D : ℕ} (a : RawIndex D) (ha : Retained D a)
    (payload : List Bool) (W : ℕ) (hW : payload.length = W) :
    (framedRecord (fixedKey a) payload).length = 2 * indexBits D + 2 * W + 2 := by
  rw [framedRecord_length, fixedKey_length a ha, hW]

end FramedRecords

section LiteralIngestion

variable {D : ℕ} {R : Type*} [Semiring R]

/-- Loading a raw literal really runs projection and pays for all source terms. -/
def ingestLiteral (slots : List (RawIndex D)) (raw : CoeffList D R) :
    CoeffList D R × ℕ := projectWithCost slots raw

theorem ingestLiteral_eq (slots : List (RawIndex D)) (raw : CoeffList D R) :
    ingestLiteral slots raw = (project slots raw, slots.length * (3 * raw.length + 2)) :=
  projectWithCost_eq slots raw

def literalFactor (D rowDegree : ℕ) : ℕ :=
  ((D + 1) * D) * (3 * (2 + (rowDegree + 1) * D) + 2)

theorem ingestLiteral_cost (slots : List (RawIndex D)) (raw : CoeffList D R)
    (hslots : slots.length = slotCount D) (rowDegree : ℕ)
    (hraw : raw.length ≤ 2 + (rowDegree + 1) * D) :
    (ingestLiteral slots raw).2 ≤ literalFactor D rowDegree * monomialCount D := by
  rw [ingestLiteral_eq, hslots]
  apply (Nat.mul_le_mul_left (slotCount D)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hraw) 2)).trans_eq
  simp only [slotCount, literalFactor]
  ring

/-- Explicit ingestion of all raw literals supplied to an expression compiler. -/
def ingestLiterals (slots : List (RawIndex D)) :
    List (CoeffList D R) → List (CoeffList D R) × ℕ
  | [] => ([], 0)
  | raw :: raws =>
    let first := ingestLiteral slots raw
    let rest := ingestLiterals slots raws
    (first.1 :: rest.1, first.2 + rest.2 + 1)

theorem ingestLiterals_value (slots : List (RawIndex D)) (raws : List (CoeffList D R)) :
    (ingestLiterals slots raws).1 = raws.map (project slots) := by
  induction raws with
  | nil => rfl
  | cons raw raws ih => simp [ingestLiterals, ingestLiteral_eq, ih]

theorem ingestLiterals_cost (slots : List (RawIndex D)) (raws : List (CoeffList D R))
    (J : ℕ) (hJ : ∀ raw ∈ raws, raw.length ≤ J) :
    (ingestLiterals slots raws).2 ≤
      raws.length * (slots.length * (3 * J + 2) + 1) := by
  induction raws with
  | nil => simp [ingestLiterals]
  | cons raw raws ih =>
    have hraw := hJ raw (by simp)
    have ht := ih (fun r hr => hJ r (by simp [hr]))
    have hc := Nat.mul_le_mul_left slots.length
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hraw) 2)
    simp only [ingestLiterals, ingestLiteral_eq, List.length_cons]
    rw [Nat.add_mul]
    omega

end LiteralIngestion

theorem ingestLiteral_correct {D : ℕ} {R : Type*} [CommSemiring R]
    (slots : List (RawIndex D)) (hn : slots.Nodup)
    (hs : ∀ a, a ∈ slots ↔ Retained D a) (raw : CoeffList D R) :
    denote (ingestLiteral slots raw).1 =
      SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1) (denote raw) := by
  rw [ingestLiteral_eq]
  simpa [denseAdd, denote] using denseAdd_denote slots hn hs raw []

section Storage

variable {D : ℕ} {R : Type*}

/-- Actual serialized key and coefficient payload length. Delimiters for the
key are included; any outer list-cell encoding overhead must still be added. -/
def storedBits (encodeCoeff : R → List Bool) (P : CoeffList D R) : ℕ :=
  (P.map fun p => (encodeIndex p.1).length + (encodeCoeff p.2).length).sum

theorem storedBits_bound (encodeCoeff : R → List Bool) (P : CoeffList D R)
    (h b : ℕ) (hkey : ∀ p ∈ P, Retained D p.1)
    (hcoeff : ∀ p ∈ P, (encodeCoeff p.2).length ≤ coefficientBits D h b) :
    storedBits encodeCoeff P ≤ P.length * slotBits D h b := by
  induction P with
  | nil => simp [storedBits]
  | cons p P ih =>
    have hk := retained_index_bits p.1 (hkey p (by simp))
    have hc := hcoeff p (by simp)
    have ht := ih (fun q hq => hkey q (by simp [hq]))
      (fun q hq => hcoeff q (by simp [hq]))
    simp only [storedBits, List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.add_mul]
    simp only [storedBits, slotBits] at ht ⊢
    omega

theorem dense_storedBits_bound (encodeCoeff : R → List Bool) (P : CoeffList D R)
    (h b : ℕ) (hkey : ∀ p ∈ P, Retained D p.1)
    (hcoeff : ∀ p ∈ P, (encodeCoeff p.2).length ≤ coefficientBits D h b)
    (hlen : P.length = slotCount D) :
    storedBits encodeCoeff P ≤
      monomialCount D * (((D + 1) * D) * slotBits D h b) := by
  have hc := storedBits_bound encodeCoeff P h b hkey hcoeff
  simpa only [hlen, slotCount, Nat.mul_assoc] using hc

end Storage

section ActualCoefficients

/-- A single explicit bound for both implemented binary base-residue operations.
The coefficient capacity is B=(D+1)b bits and the modulus may use one extra bit. -/
def baseEventBudget (D b : ℕ) : ℕ :=
  200 * ((D + 1) * b + 2) ^ 2 + 3 * ((D + 1) * b)

theorem base_mul_events (D b : ℕ) (m xs ys : List Bool)
    (hm : m.length ≤ (D + 1) * b + 1)
    (hx : xs.length ≤ (D + 1) * b) (hy : ys.length ≤ (D + 1) * b) :
    (SubexponentialSAT.SubexpLiftRing.mulBaseRun ((D + 1) * b) m xs ys).2 ≤ baseEventBudget D b :=
  SubexponentialSAT.SubexpLiftRing.mulBaseRun_cost _ _ _ _ hm hx hy

theorem base_add_events (D b : ℕ) (m xs ys : List Bool)
    (hm : m.length ≤ (D + 1) * b + 1)
    (hx : xs.length ≤ (D + 1) * b) (hy : ys.length ≤ (D + 1) * b) :
    (SubexponentialSAT.SubexpLiftRing.addBaseRun ((D + 1) * b) m xs ys).2 ≤ baseEventBudget D b := by
  have hc := SubexponentialSAT.SubexpLiftRing.addBaseRun_cost ((D + 1) * b) m xs ys hm hx hy
  unfold baseEventBudget
  omega

/-- The exponent four is absolute; it does not depend on p, h, D, or k. -/
theorem baseEventBudget_degree (D h b : ℕ) :
    baseEventBudget D b ≤ 203 * parameterSize D h b ^ 4 := by
  let S := parameterSize D h b
  have hS : 1 ≤ S := by dsimp [S, parameterSize]; omega
  have hB : (D + 1) * b + 2 ≤ S ^ 2 := by
    dsimp [S, parameterSize]
    ring_nf
    omega
  have hsquare := Nat.pow_le_pow_left hB 2
  have hpow : (S ^ 2) ^ 2 = S ^ 4 := by ring
  rw [hpow] at hsquare
  have hsmall : (D + 1) * b ≤ S ^ 4 :=
    (by omega : (D + 1) * b ≤ S ^ 2).trans
      (Nat.pow_le_pow_right hS (by decide))
  calc
    baseEventBudget D b ≤ 200 * S ^ 4 + 3 * S ^ 4 :=
      Nat.add_le_add (Nat.mul_le_mul_left 200 hsquare) (Nat.mul_le_mul_left 3 hsmall)
    _ = 203 * S ^ 4 := by ring

def quarticEventBudget (D b : ℕ) : ℕ := 49 * baseEventBudget D b

def binaryQuarticAdd (p D : ℕ) [Fact p.Prime]
    (a b : SubexponentialSAT.SubexpQuarticRing.Quad
      (SubexponentialSAT.SubexpQuarticRing.Word (SubexponentialSAT.SubexpLiftRing.baseWidth p (D + 1)))) :=
  SubexponentialSAT.SubexpQuarticRing.addRun (SubexponentialSAT.SubexpQuarticRing.wordAdd p (D + 1)) a b

theorem binaryQuarticAdd_correct (p D : ℕ) [Fact p.Prime]
    (a b : SubexponentialSAT.SubexpQuarticRing.Quad
      (SubexponentialSAT.SubexpQuarticRing.Word (SubexponentialSAT.SubexpLiftRing.baseWidth p (D + 1)))) :
    ((binaryQuarticAdd p D a b).1).map (SubexponentialSAT.SubexpQuarticRing.wordValue p (D + 1)) =
      SubexponentialSAT.SubexpQuarticRing.add
        (a.map (SubexponentialSAT.SubexpQuarticRing.wordValue p (D + 1)))
        (b.map (SubexponentialSAT.SubexpQuarticRing.wordValue p (D + 1))) :=
  SubexponentialSAT.SubexpQuarticRing.addRun_correct (SubexponentialSAT.SubexpQuarticRing.wordValue p (D + 1))
    (SubexponentialSAT.SubexpQuarticRing.wordAdd p (D + 1))
    (SubexponentialSAT.SubexpQuarticRing.wordAdd_correct p (D + 1)) a b

theorem quartic_add_events (p D : ℕ) [Fact p.Prime]
    (a b : SubexponentialSAT.SubexpQuarticRing.Quad
      (SubexponentialSAT.SubexpQuarticRing.Word (SubexponentialSAT.SubexpLiftRing.baseWidth p (D + 1)))) :
    (binaryQuarticAdd p D a b).2 ≤ quarticEventBudget D (Nat.log 2 p + 1) := by
  have h := SubexponentialSAT.SubexpQuarticRing.addRun_cost
    (SubexponentialSAT.SubexpQuarticRing.wordAdd p (D + 1))
    (SubexponentialSAT.SubexpQuarticRing.scalarBudget p (D + 1))
    (SubexponentialSAT.SubexpQuarticRing.wordAdd_cost p (D + 1)) a b
  apply h.trans
  change 4 * baseEventBudget D (Nat.log 2 p + 1) ≤
    49 * baseEventBudget D (Nat.log 2 p + 1)
  omega

/-- This bounds the already implemented binary quartet multiplication,
including its Horner reduction. There is no abstract scalar multiplication
hidden in this particular counter. -/
theorem quartic_mul_events (p D : ℕ) [Fact p.Prime]
    (t a b : SubexponentialSAT.SubexpQuarticRing.Quad
      (SubexponentialSAT.SubexpQuarticRing.Word (SubexponentialSAT.SubexpLiftRing.baseWidth p (D + 1)))) :
    (SubexponentialSAT.SubexpQuarticRing.binaryMul p (D + 1) t a b).2 ≤
      quarticEventBudget D (Nat.log 2 p + 1) :=
  SubexponentialSAT.SubexpQuarticRing.binaryMul_cost p (D + 1) t a b

theorem quarticEventBudget_degree (D h b : ℕ) :
    quarticEventBudget D b ≤ 9947 * parameterSize D h b ^ 4 := by
  have hb := Nat.mul_le_mul_left 49 (baseEventBudget_degree D h b)
  simpa only [quarticEventBudget, ← Nat.mul_assoc] using hb

theorem quartic_weighted_dense_events (D b : ℕ) :
    quarticEventBudget D b * denseCost (slotCount D) ≤
      (99470 * parameterSize D 4 b ^ 10) * monomialCount D ^ 4 := by
  simpa using weighted_dense_events_degree D 4 b (quarticEventBudget D b) 9947 4
    (quarticEventBudget_degree D 4 b)

/-- Instantiate the storage bound with the actual injective prime-power
extension-ring encoding. Its construction/evaluation cost is separate. -/
theorem lambda_storedBits_bound (p h D : ℕ) [Fact p.Prime] (hh : h ≠ 0)
    (P : CoeffList D (SubexponentialSAT.ActualLiftRing.Ring p h (D + 1)))
    (hkey : ∀ t ∈ P, Retained D t.1) (hlen : P.length = slotCount D) :
    storedBits (SubexponentialSAT.SubexpLiftRing.encodeLambda p h (D + 1) (by omega)) P ≤
      monomialCount D * (((D + 1) * D) *
        slotBits D h (Nat.log 2 p + 1)) := by
  apply dense_storedBits_bound _ P h (Nat.log 2 p + 1) hkey _ hlen
  intro t ht
  rw [SubexponentialSAT.SubexpLiftRing.encodeLambda_length _ _ _ _ hh]
  simp only [coefficientBits, Nat.mul_assoc]
  exact le_rfl

/-- The already proved quotient encoding, now packaged for record scanning. -/
noncomputable def coefficientBlockCode (p h D : ℕ) [Fact p.Prime] (hh : h ≠ 0) :
    SubexponentialSAT.StackEncoding.BlockCode (SubexponentialSAT.ActualLiftRing.Ring p h (D + 1)) where
  width := coefficientBits D h (Nat.log 2 p + 1)
  width_pos := Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hh) (by omega)) (by omega)
  block := SubexponentialSAT.SubexpLiftRing.encodeLambda p h (D + 1) (by omega)
  length_block x := by
    rw [SubexponentialSAT.SubexpLiftRing.encodeLambda_length _ _ _ _ hh]
    simp [coefficientBits, Nat.mul_assoc]
  injective_block := SubexponentialSAT.SubexpLiftRing.encodeLambda_injective p h (D + 1) (by omega)

noncomputable def coefficientRecordCode (p h D : ℕ) [Fact p.Prime] (hh : h ≠ 0) :
    SubexponentialSAT.StackEncoding.BlockCode (RetainedKey D × SubexponentialSAT.ActualLiftRing.Ring p h (D + 1)) :=
  recordBlockCode (keyBlockCode D) (coefficientBlockCode p h D hh)

theorem coefficientRecordCode_width (p h D : ℕ) [Fact p.Prime] (hh : h ≠ 0) :
    (coefficientRecordCode p h D hh).width = slotBits D h (Nat.log 2 p + 1) := rfl

end ActualCoefficients

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

/-- An actual coefficient implementation with a semantic decoder. No ring laws
are postulated on code words. Each operation returns its own measured counter. -/
structure RepresentedRing (C R : Type*) [CommRing R] where
  decode : C → R
  zeroRun : C × ℕ
  oneRun : C × ℕ
  addRun : C → C → C × ℕ
  mulRun : C → C → C × ℕ
  negRun : C → C × ℕ
  zero_correct : decode zeroRun.1 = 0
  one_correct : decode oneRun.1 = 1
  add_correct : ∀ a b, decode (addRun a b).1 = decode a + decode b
  mul_correct : ∀ a b, decode (mulRun a b).1 = decode a * decode b
  neg_correct : ∀ a, decode (negRun a).1 = -decode a

open SubexponentialSAT.SymbolicCost

section RepresentedLists

variable {D : ℕ} {C R : Type*} [CommRing R] (ops : RepresentedRing C R)

def decodeList (P : CoeffList D C) : CoeffList D R :=
  P.map fun p => (p.1, ops.decode p.2)

def representedScan : CoeffList D C → RawIndex D → C × ℕ
  | [], _ => ops.zeroRun
  | (b, c) :: P, a =>
    let rest := representedScan P a
    if b = a then
      let out := ops.addRun c rest.1
      (out.1, rest.2 + out.2 + 2)
    else (rest.1, rest.2 + 2)

def representedProject : List (RawIndex D) → CoeffList D C → CoeffList D C × ℕ
  | [], _ => ([], 0)
  | a :: slots, P =>
    let value := representedScan ops P a
    let rest := representedProject slots P
    ((a, value.1) :: rest.1, value.2 + rest.2 + 2)

def representedRow (p : RawIndex D × C) : CoeffList D C → CoeffList D C × ℕ
  | [] => ([], 0)
  | q :: Q =>
    let value := ops.mulRun p.2 q.2
    let rest := representedRow p Q
    ((p.1 + q.1, value.1) :: rest.1, value.2 + rest.2 + 2)

def representedRawMul : CoeffList D C → CoeffList D C → CoeffList D C × ℕ
  | [], _ => ([], 0)
  | p :: P, Q =>
    let row := representedRow ops p Q
    let rest := representedRawMul P Q
    let joined := appendWithCost row.1 rest.1
    (joined.1, row.2 + rest.2 + joined.2 + 1)

def representedAdd (slots : List (RawIndex D)) (P Q : CoeffList D C) : CoeffList D C × ℕ :=
  let joined := appendWithCost P Q
  let out := representedProject ops slots joined.1
  (out.1, joined.2 + out.2)

def representedMul (slots : List (RawIndex D)) (P Q : CoeffList D C) : CoeffList D C × ℕ :=
  let pairs := representedRawMul ops P Q
  let out := representedProject ops slots pairs.1
  (out.1, pairs.2 + out.2)

@[simp] theorem decodeList_append (P Q : CoeffList D C) :
    decodeList ops (P ++ Q) = decodeList ops P ++ decodeList ops Q := by simp [decodeList]

@[simp] theorem decodeList_length (P : CoeffList D C) :
    (decodeList ops P).length = P.length := by simp [decodeList]

theorem representedScan_correct (P : CoeffList D C) (a : RawIndex D) :
    ops.decode (representedScan ops P a).1 = coeff (decodeList ops P) a := by
  induction P with
  | nil => simpa [representedScan, decodeList, coeff] using ops.zero_correct
  | cons p P ih =>
    rcases p with ⟨b, c⟩
    by_cases h : b = a
    · simp only [representedScan, ite_eq_left h, ops.add_correct, ih, decodeList,
        List.map_cons, coeff]
    · simp only [representedScan, ite_eq_right h, decodeList, List.map_cons, coeff]
      simpa only [decodeList, zero_add] using ih

theorem representedProject_correct (slots : List (RawIndex D)) (P : CoeffList D C) :
    decodeList ops (representedProject ops slots P).1 = project slots (decodeList ops P) := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
    change (a, ops.decode (representedScan ops P a).1) ::
      decodeList ops (representedProject ops slots P).1 = _
    rw [representedScan_correct, ih]
    rfl

theorem representedProject_length (slots : List (RawIndex D)) (P : CoeffList D C) :
    (representedProject ops slots P).1.length = slots.length := by
  rw [← decodeList_length ops, representedProject_correct, length_project]

theorem representedRow_correct (p : RawIndex D × C) (Q : CoeffList D C) :
    decodeList ops (representedRow ops p Q).1 =
      rowMul (p.1, ops.decode p.2) (decodeList ops Q) := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    rcases q with ⟨a, c⟩
    change (p.1 + a, ops.decode (ops.mulRun p.2 c).1) ::
      decodeList ops (representedRow ops p Q).1 = _
    rw [ops.mul_correct, ih]
    rfl

theorem representedRow_length (p : RawIndex D × C) (Q : CoeffList D C) :
    (representedRow ops p Q).1.length = Q.length := by
  rw [← decodeList_length ops, representedRow_correct, length_rowMul, decodeList_length]

theorem representedRawMul_correct (P Q : CoeffList D C) :
    decodeList ops (representedRawMul ops P Q).1 = rawMul (decodeList ops P) (decodeList ops Q) := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rcases p with ⟨a, c⟩
    simp only [representedRawMul, appendWithCost_eq, decodeList_append,
      representedRow_correct, ih]
    rfl

theorem representedRawMul_length (P Q : CoeffList D C) :
    (representedRawMul ops P Q).1.length = P.length * Q.length := by
  rw [← decodeList_length ops, representedRawMul_correct, length_rawMul,
    decodeList_length, decodeList_length]

theorem representedAdd_correct (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    decodeList ops (representedAdd ops slots P Q).1 =
      denseAdd slots (decodeList ops P) (decodeList ops Q) := by
  simp [representedAdd, appendWithCost_eq, representedProject_correct, denseAdd]

theorem representedMul_correct (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    decodeList ops (representedMul ops slots P Q).1 =
      denseMul slots (decodeList ops P) (decodeList ops Q) := by
  simp [representedMul, representedProject_correct, representedRawMul_correct, denseMul]

theorem representedMul_denote (slots : List (RawIndex D)) (hn : slots.Nodup)
    (hs : ∀ a, a ∈ slots ↔ Retained D a) (P Q : CoeffList D C) :
    denote (decodeList ops (representedMul ops slots P Q).1) =
      SubexponentialSAT.Truncation.canonical (D + 1) D (2 * D + 1)
        (denote (decodeList ops P) * denote (decodeList ops Q)) := by
  rw [representedMul_correct]
  exact denseMul_denote slots hn hs _ _

/-- Independent per-call bounds for the concrete scalar routines. -/
structure ScalarBudget (q : ℕ) : Prop where
  zero : ops.zeroRun.2 ≤ q
  one : ops.oneRun.2 ≤ q
  add : ∀ a b, (ops.addRun a b).2 ≤ q
  mul : ∀ a b, (ops.mulRun a b).2 ≤ q
  neg : ∀ a, (ops.negRun a).2 ≤ q

variable {q : ℕ} (budget : ScalarBudget ops q)

include budget

theorem representedScan_cost (P : CoeffList D C) (a : RawIndex D) :
    (representedScan ops P a).2 ≤ (q + 2) * P.length + q := by
  induction P with
  | nil => simpa [representedScan] using budget.zero
  | cons p P ih =>
    rcases p with ⟨b, c⟩
    have hc := budget.add c (representedScan ops P a).1
    by_cases h : b = a <;>
      simp only [representedScan, h, ↓reduceIte, List.length_cons,
        Nat.mul_add, Nat.mul_one] <;> omega

theorem representedProject_cost (slots : List (RawIndex D)) (P : CoeffList D C) :
    (representedProject ops slots P).2 ≤ slots.length * ((q + 2) * P.length + q + 2) := by
  induction slots with
  | nil => simp [representedProject]
  | cons a slots ih =>
    have hc := representedScan_cost ops budget P a
    simp only [representedProject, List.length_cons]
    calc
      _ ≤ ((q + 2) * P.length + q) +
          slots.length * ((q + 2) * P.length + q + 2) + 2 :=
        Nat.add_le_add_right (Nat.add_le_add hc ih) 2
      _ = _ := by ring

theorem representedRow_cost (p : RawIndex D × C) (Q : CoeffList D C) :
    (representedRow ops p Q).2 ≤ (q + 2) * Q.length := by
  induction Q with
  | nil => simp [representedRow]
  | cons a Q ih =>
    have hc := budget.mul p.2 a.2
    simp only [representedRow, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem representedRawMul_cost (P Q : CoeffList D C) :
    (representedRawMul ops P Q).2 ≤ (q + 3) * P.length * Q.length + P.length := by
  induction P with
  | nil => simp [representedRawMul]
  | cons p P ih =>
    have hc := representedRow_cost ops budget p Q
    simp only [representedRawMul, appendWithCost_eq,
      representedRow_length, List.length_cons]
    calc
      _ ≤ (q + 2) * Q.length + ((q + 3) * P.length * Q.length + P.length) + Q.length + 1 := by omega
      _ = _ := by ring

theorem representedMul_cost (slots : List (RawIndex D)) (P Q : CoeffList D C)
    (hP : P.length = slots.length) (hQ : Q.length = slots.length) :
    (representedMul ops slots P Q).2 ≤ (q + 3) * denseCost slots.length := by
  have hr := representedRawMul_cost ops budget P Q
  have hp := representedProject_cost ops budget slots (representedRawMul ops P Q).1
  rw [representedRawMul_length] at hp
  change (representedRawMul ops P Q).2 +
    (representedProject ops slots (representedRawMul ops P Q).1).2 ≤ _
  apply (Nat.add_le_add hr hp).trans
  rw [hP, hQ]
  unfold denseCost
  ring_nf
  omega

theorem representedAdd_cost (slots : List (RawIndex D)) (P Q : CoeffList D C)
    (hP : P.length = slots.length) (hQ : Q.length = slots.length) :
    (representedAdd ops slots P Q).2 ≤ (q + 3) * denseAddCost slots.length := by
  have hp := representedProject_cost ops budget slots (P ++ Q)
  simp only [List.length_append] at hp
  simp only [representedAdd, appendWithCost_eq ]
  apply (Nat.add_le_add_left hp P.length).trans
  rw [hP, hQ]
  unfold denseAddCost
  ring_nf
  omega

theorem representedMul_uniform (slots : List (RawIndex D)) (P Q : CoeffList D C)
    (hP : P.length = slots.length) (hQ : Q.length = slots.length)
    (hslots : slots.length = slotCount D) :
    (representedMul ops slots P Q).2 ≤
      ((q + 3) * listFactor D) * monomialCount D ^ 4 := by
  apply (representedMul_cost ops budget slots P Q hP hQ).trans
  rw [hslots]
  exact weighted_dense_events_uniform D (q + 3)

end RepresentedLists

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

/-- Executable callbacks only. The semantic decoder is deliberately absent. -/
structure RingProgram (C : Type*) where
  zeroRun : C × ℕ
  oneRun : C × ℕ
  addRun : C → C → C × ℕ
  mulRun : C → C → C × ℕ
  negRun : C → C × ℕ

abbrev RepresentedRing.program {C R : Type*} [CommRing R] (ops : RepresentedRing C R) :
    RingProgram C :=
  ⟨ops.zeroRun, ops.oneRun, ops.addRun, ops.mulRun, ops.negRun⟩

open SubexponentialSAT.SymbolicCost

section ProgramLists

variable {D : ℕ} {C : Type*} (ops : RingProgram C)

def programScan : CoeffList D C → RawIndex D → C × ℕ
  | [], _ => ops.zeroRun
  | (b, c) :: P, a =>
    let rest := programScan P a
    if b = a then
      let out := ops.addRun c rest.1
      (out.1, rest.2 + out.2 + 2)
    else (rest.1, rest.2 + 2)

def programProject : List (RawIndex D) → CoeffList D C → CoeffList D C × ℕ
  | [], _ => ([], 0)
  | a :: slots, P =>
    let value := programScan ops P a
    let rest := programProject slots P
    ((a, value.1) :: rest.1, value.2 + rest.2 + 2)

def programRow (p : RawIndex D × C) : CoeffList D C → CoeffList D C × ℕ
  | [] => ([], 0)
  | q :: Q =>
    let value := ops.mulRun p.2 q.2
    let rest := programRow p Q
    ((p.1 + q.1, value.1) :: rest.1, value.2 + rest.2 + 2)

def programRawMul : CoeffList D C → CoeffList D C → CoeffList D C × ℕ
  | [], _ => ([], 0)
  | p :: P, Q =>
    let row := programRow ops p Q
    let rest := programRawMul P Q
    let joined := appendWithCost row.1 rest.1
    (joined.1, row.2 + rest.2 + joined.2 + 1)

def programAdd (slots : List (RawIndex D)) (P Q : CoeffList D C) : CoeffList D C × ℕ :=
  let joined := appendWithCost P Q
  let out := programProject ops slots joined.1
  (out.1, joined.2 + out.2)

def programMul (slots : List (RawIndex D)) (P Q : CoeffList D C) : CoeffList D C × ℕ :=
  let pairs := programRawMul ops P Q
  let out := programProject ops slots pairs.1
  (out.1, pairs.2 + out.2)

end ProgramLists

section ProgramRefinement

variable {D : ℕ} {C R : Type*} [CommRing R] (ops : RepresentedRing C R)

@[simp] theorem programScan_represented (P : CoeffList D C) (a : RawIndex D) :
    programScan ops.program P a = representedScan ops P a := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    cases p
    simp only [programScan, representedScan]
    rw [ih]

@[simp] theorem programProject_represented (slots : List (RawIndex D)) (P : CoeffList D C) :
    programProject ops.program slots P = representedProject ops slots P := by
  induction slots with
  | nil => rfl
  | cons a slots ih => simp only [programProject, representedProject, programScan_represented, ih]

@[simp] theorem programRow_represented (p : RawIndex D × C) (Q : CoeffList D C) :
    programRow ops.program p Q = representedRow ops p Q := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    simp only [programRow, representedRow]
    rw [ih]

@[simp] theorem programRawMul_represented (P Q : CoeffList D C) :
    programRawMul ops.program P Q = representedRawMul ops P Q := by
  induction P with
  | nil => rfl
  | cons p P ih => simp only [programRawMul, representedRawMul, programRow_represented, ih]

@[simp] theorem programAdd_represented (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    programAdd ops.program slots P Q = representedAdd ops slots P Q := by
  simp only [programAdd, representedAdd, programProject_represented]

@[simp] theorem programMul_represented (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    programMul ops.program slots P Q = representedMul ops slots P Q := by
  simp only [programMul, representedMul, programProject_represented, programRawMul_represented]

end ProgramRefinement

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

open SubexponentialSAT.SymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Actual coefficient data: four fixed-width binary words. -/
abbrev QuarticCode (p D : ℕ) := Quad (Word (baseWidth p (D + 1)))

/-- Repeated arithmetic uses only supplied modulus, reduction, and constant
caches. Returning a cached constant charges no scalar arithmetic; a concrete
stack implementation must additionally charge copying its bits. -/
def preparedProgram (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t z o : QuarticCode p D) : RingProgram (QuarticCode p D) where
  zeroRun := (z, 0)
  oneRun := (o, 0)
  addRun := SubexpPreparedQuartic.binaryAdd p (D + 1) M
  mulRun := SubexpPreparedQuartic.binaryMul p (D + 1) M t
  negRun := SubexpPreparedQuartic.binaryNeg p (D + 1) M

/-- The semantic certificate is separate from the executable program. -/
noncomputable def preparedRing (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (c : Fin 4 → ZMod (p ^ (D + 1))) (t z o : QuarticCode p D)
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : quotientDenote c (z.map (wordValue p (D + 1))) = 0)
    (ho : quotientDenote c (o.map (wordValue p (D + 1))) = 1) :
    RepresentedRing (QuarticCode p D) (LiftRing.Extension (QuarticSearch.poly c)) where
  decode a := quotientDenote c (a.map (wordValue p (D + 1)))
  zeroRun := (z, 0)
  oneRun := (o, 0)
  addRun := SubexpPreparedQuartic.binaryAdd p (D + 1) M
  mulRun := SubexpPreparedQuartic.binaryMul p (D + 1) M t
  negRun := SubexpPreparedQuartic.binaryNeg p (D + 1) M
  zero_correct := hz
  one_correct := ho
  add_correct := SubexpPreparedQuartic.binaryAdd_quotient p (D + 1) M c
  mul_correct a b := SubexpPreparedQuartic.binaryMul_quotient p (D + 1) M c t a b ht
  neg_correct := SubexpPreparedQuartic.binaryNeg_quotient p (D + 1) M c

section PreparedRefinement

variable (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (c : Fin 4 → ZMod (p ^ (D + 1))) (t z o : QuarticCode p D)
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : quotientDenote c (z.map (wordValue p (D + 1))) = 0)
    (ho : quotientDenote c (o.map (wordValue p (D + 1))) = 1)

@[simp] theorem preparedRing_program :
    (preparedRing p D M c t z o ht hz ho).program = preparedProgram p D M t z o := rfl

theorem preparedRing_budget :
    ScalarBudget (preparedRing p D M c t z o ht hz ho)
      (quarticEventBudget D (Nat.log 2 p + 1)) := by
  constructor
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · intro a b
    apply (SubexpPreparedQuartic.binaryAdd_cost p (D + 1) M a b).trans
    change 4 * scalarBudget p (D + 1) ≤ 49 * scalarBudget p (D + 1)
    omega
  · exact SubexpPreparedQuartic.binaryMul_cost p (D + 1) M t
  · intro a
    apply (SubexpPreparedQuartic.binaryNeg_cost p (D + 1) M a).trans
    change 4 * scalarBudget p (D + 1) ≤ 49 * scalarBudget p (D + 1)
    omega

theorem preparedProgram_mul_correct (slots : List (RawIndex D))
    (P Q : CoeffList D (QuarticCode p D)) :
    decodeList (preparedRing p D M c t z o ht hz ho)
        (programMul (preparedProgram p D M t z o) slots P Q).1 =
      denseMul slots (decodeList (preparedRing p D M c t z o ht hz ho) P)
        (decodeList (preparedRing p D M c t z o ht hz ho) Q) := by
  rw [← preparedRing_program p D M c t z o ht hz ho, programMul_represented]
  exact representedMul_correct _ _ _ _

include c ht hz ho in
theorem preparedProgram_mul_cost (slots : List (RawIndex D))
    (P Q : CoeffList D (QuarticCode p D))
    (hP : P.length = slots.length) (hQ : Q.length = slots.length) :
    (programMul (preparedProgram p D M t z o) slots P Q).2 ≤
      (quarticEventBudget D (Nat.log 2 p + 1) + 3) * denseCost slots.length := by
  rw [← preparedRing_program p D M c t z o ht hz ho, programMul_represented]
  exact representedMul_cost _ (preparedRing_budget p D M c t z o ht hz ho) _ _ _ hP hQ

end PreparedRefinement

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

open SubexponentialSAT.SymbolicCost

/-- Bounds on executable callbacks require no decoder or algebraic laws. -/
structure ProgramBudget {C : Type*} (ops : RingProgram C) (q : ℕ) : Prop where
  zero : ops.zeroRun.2 ≤ q
  one : ops.oneRun.2 ≤ q
  add : ∀ a b, (ops.addRun a b).2 ≤ q
  mul : ∀ a b, (ops.mulRun a b).2 ≤ q
  neg : ∀ a, (ops.negRun a).2 ≤ q

theorem ScalarBudget.program {C R : Type*} [CommRing R] {ops : RepresentedRing C R}
    {q : ℕ} (h : ScalarBudget ops q) : ProgramBudget ops.program q :=
  ⟨h.zero, h.one, h.add, h.mul, h.neg⟩

abbrev BitCoeffList (C : Type*) := List (List Bool × C)

def encodeProgramList {D : ℕ} {C : Type*} (P : CoeffList D C) : BitCoeffList C :=
  P.map fun p => (encodeIndex p.1, p.2)

@[simp] theorem encodeProgramList_length {D : ℕ} {C : Type*} (P : CoeffList D C) :
    (encodeProgramList P).length = P.length := by simp [encodeProgramList]

@[simp] theorem encodeProgramList_append {D : ℕ} {C : Type*} (P Q : CoeffList D C) :
    encodeProgramList (P ++ Q) = encodeProgramList P ++ encodeProgramList Q := by
  simp [encodeProgramList]

section BitLists

variable {C : Type*} (ops : RingProgram C)

/-- Equality reads the actual requested and stored key bits. -/
def bitScan : BitCoeffList C → List Bool → C × ℕ
  | [], _ => ops.zeroRun
  | (key, c) :: P, a =>
    let rest := bitScan P a
    let check := equalBitsWithCost a key
    if check.1 then
      let out := ops.addRun c rest.1
      (out.1, rest.2 + check.2 + out.2 + 2)
    else (rest.1, rest.2 + check.2 + 2)

def bitProject : List (List Bool) → BitCoeffList C → BitCoeffList C × ℕ
  | [], _ => ([], 0)
  | a :: slots, P =>
    let value := bitScan ops P a
    let rest := bitProject slots P
    ((a, value.1) :: rest.1, value.2 + rest.2 + 2)

/-- Product exponents are formed by the direct bit-string adder. -/
def bitRow (p : List Bool × C) : BitCoeffList C → BitCoeffList C × ℕ
  | [] => ([], 0)
  | q :: Q =>
    let key := addIndexBits p.1 q.1
    let value := ops.mulRun p.2 q.2
    let rest := bitRow p Q
    ((key.1, value.1) :: rest.1, key.2 + value.2 + rest.2 + 2)

def bitRawMul : BitCoeffList C → BitCoeffList C → BitCoeffList C × ℕ
  | [], _ => ([], 0)
  | p :: P, Q =>
    let row := bitRow ops p Q
    let rest := bitRawMul P Q
    let joined := appendWithCost row.1 rest.1
    (joined.1, row.2 + rest.2 + joined.2 + 1)

def bitAdd (slots : List (List Bool)) (P Q : BitCoeffList C) : BitCoeffList C × ℕ :=
  let joined := appendWithCost P Q
  let out := bitProject ops slots joined.1
  (out.1, joined.2 + out.2)

def bitMul (slots : List (List Bool)) (P Q : BitCoeffList C) : BitCoeffList C × ℕ :=
  let pairs := bitRawMul ops P Q
  let out := bitProject ops slots pairs.1
  (out.1, pairs.2 + out.2)

end BitLists

section BitRefinement

variable {D : ℕ} {C : Type*} (ops : RingProgram C)

theorem bitScan_correct (P : CoeffList D C) (a : RawIndex D) :
    (bitScan ops (encodeProgramList P) (encodeIndex a)).1 =
      (programScan ops P a).1 := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rcases p with ⟨b, c⟩
    have h : (equalBitsWithCost (encodeIndex a) (encodeIndex b)).1 = true ↔ b = a := by
      rw [encodedIndexEquality_correct]
      exact eq_comm
    simp only [encodeProgramList, List.map_cons] at ih ⊢
    simp only [bitScan, programScan, h, ih]
    by_cases hba : b = a <;> simp only [hba, ↓reduceIte]

theorem bitProject_correct (slots : List (RawIndex D)) (P : CoeffList D C) :
    (bitProject ops (slots.map encodeIndex) (encodeProgramList P)).1 =
      encodeProgramList (programProject ops slots P).1 := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
    simp only [List.map_cons, bitProject, programProject, bitScan_correct, ih]
    rfl

theorem bitRow_correct (p : RawIndex D × C) (Q : CoeffList D C) :
    (bitRow ops (encodeIndex p.1, p.2) (encodeProgramList Q)).1 =
      encodeProgramList (programRow ops p Q).1 := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    rcases q with ⟨a, c⟩
    simp only [encodeProgramList, List.map_cons] at ih ⊢
    simp only [bitRow, programRow, addIndexBits_correct, ih, List.map_cons]

theorem bitRawMul_correct (P Q : CoeffList D C) :
    (bitRawMul ops (encodeProgramList P) (encodeProgramList Q)).1 =
      encodeProgramList (programRawMul ops P Q).1 := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rcases p with ⟨a, c⟩
    change (bitRawMul ops ((encodeIndex a, c) :: encodeProgramList P)
      (encodeProgramList Q)).1 = _
    simp only [bitRawMul, programRawMul, appendWithCost_eq, ih, encodeProgramList_append]
    rw [bitRow_correct ops (a, c) Q]

theorem bitAdd_correct (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    (bitAdd ops (slots.map encodeIndex) (encodeProgramList P) (encodeProgramList Q)).1 =
      encodeProgramList (programAdd ops slots P Q).1 := by
  simp only [bitAdd, programAdd, appendWithCost_eq,
    ← encodeProgramList_append, bitProject_correct]

theorem bitMul_correct (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    (bitMul ops (slots.map encodeIndex) (encodeProgramList P) (encodeProgramList Q)).1 =
      encodeProgramList (programMul ops slots P Q).1 := by
  simp only [bitMul, programMul, bitRawMul_correct, bitProject_correct]

end BitRefinement

section BitCounts

variable {C : Type*} (ops : RingProgram C) {q I : ℕ} (budget : ProgramBudget ops q)

theorem bitProject_length (slots : List (List Bool)) (P : BitCoeffList C) :
    (bitProject ops slots P).1.length = slots.length := by
  induction slots with
  | nil => rfl
  | cons a slots ih => simpa only [bitProject, List.length_cons] using congrArg Nat.succ ih

theorem bitRow_length (p : List Bool × C) (Q : BitCoeffList C) :
    (bitRow ops p Q).1.length = Q.length := by
  induction Q with
  | nil => rfl
  | cons a Q ih => simpa only [bitRow, List.length_cons] using congrArg Nat.succ ih

theorem bitRawMul_length (P Q : BitCoeffList C) :
    (bitRawMul ops P Q).1.length = P.length * Q.length := by
  induction P with
  | nil => simp [bitRawMul]
  | cons p P ih =>
    simp only [bitRawMul, appendWithCost_eq, List.length_append, bitRow_length, ih,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

include budget

theorem bitScan_cost (P : BitCoeffList C) (a : List Bool) (ha : a.length ≤ I) :
    (bitScan ops P a).2 ≤ (q + I + 3) * P.length + q := by
  induction P with
  | nil => simpa only [bitScan, List.length_nil, Nat.mul_zero, Nat.zero_add] using budget.zero
  | cons p P ih =>
    rcases p with ⟨key, c⟩
    have he := equalBitsWithCost_le a key
    have hc := budget.add c (bitScan ops P a).1
    by_cases h : (equalBitsWithCost a key).1 = true <;>
      simp [bitScan, h, Nat.mul_add ] <;> omega

theorem bitProject_cost (slots : List (List Bool)) (P : BitCoeffList C)
    (hs : ∀ a ∈ slots, a.length ≤ I) :
    (bitProject ops slots P).2 ≤ slots.length * ((q + I + 3) * P.length + q + 2) := by
  revert hs
  induction slots with
  | nil => intro _; simp [bitProject]
  | cons a slots ih =>
    intro hs
    have hc := bitScan_cost ops budget P a (hs a (by simp))
    have ht := ih (fun a ha => hs a (by simp [ha]))
    simp only [bitProject, List.length_cons]
    calc
      _ ≤ ((q + I + 3) * P.length + q) +
          slots.length * ((q + I + 3) * P.length + q + 2) + 2 :=
        Nat.add_le_add_right (Nat.add_le_add hc ht) 2
      _ = _ := by ring

theorem bitRow_cost (p : List Bool × C) (Q : BitCoeffList C)
    (hp : p.1.length ≤ I) (hQ : ∀ a ∈ Q, a.1.length ≤ I) :
    (bitRow ops p Q).2 ≤ (q + 6 * I + 3) * Q.length := by
  revert hQ
  induction Q with
  | nil => intro _; simp [bitRow]
  | cons a Q ih =>
    intro hQ
    have ht := ih (fun a ha => hQ a (by simp [ha]))
    have ha := hQ a (by simp)
    have he := addIndexBits_cost p.1 a.1
    have hc := budget.mul p.2 a.2
    simp only [bitRow, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem bitRawMul_cost (P Q : BitCoeffList C)
    (hP : ∀ a ∈ P, a.1.length ≤ I) (hQ : ∀ a ∈ Q, a.1.length ≤ I) :
    (bitRawMul ops P Q).2 ≤ (q + 6 * I + 4) * P.length * Q.length + P.length := by
  revert hP
  induction P with
  | nil => intro _; simp [bitRawMul]
  | cons p P ih =>
    intro hP
    have ht := ih (fun a ha => hP a (by simp [ha]))
    have hc := bitRow_cost ops budget p Q (hP p (by simp)) hQ
    simp only [bitRawMul, appendWithCost_eq, bitRow_length, List.length_cons]
    calc
      _ ≤ (q + 6 * I + 3) * Q.length +
          ((q + 6 * I + 4) * P.length * Q.length + P.length) + Q.length + 1 := by omega
      _ = _ := by ring

theorem bitMul_cost (slots : List (List Bool)) (P Q : BitCoeffList C)
    (hs : ∀ a ∈ slots, a.length ≤ I)
    (hP : ∀ a ∈ P, a.1.length ≤ I) (hQ : ∀ a ∈ Q, a.1.length ≤ I)
    (hlenP : P.length = slots.length) (hlenQ : Q.length = slots.length) :
    (bitMul ops slots P Q).2 ≤ (q + 6 * I + 5) * denseCost slots.length := by
  have hr := bitRawMul_cost ops budget P Q hP hQ
  have hp := bitProject_cost ops budget slots (bitRawMul ops P Q).1 hs
  rw [bitRawMul_length] at hp
  change (bitRawMul ops P Q).2 + (bitProject ops slots (bitRawMul ops P Q).1).2 ≤ _
  apply (Nat.add_le_add hr hp).trans
  rw [hlenP, hlenQ]
  unfold denseCost
  ring_nf
  omega

theorem bitAdd_cost (slots : List (List Bool)) (P Q : BitCoeffList C)
    (hs : ∀ a ∈ slots, a.length ≤ I)
    (hlenP : P.length = slots.length) (hlenQ : Q.length = slots.length) :
    (bitAdd ops slots P Q).2 ≤ (q + 6 * I + 5) * denseAddCost slots.length := by
  have hp := bitProject_cost ops budget slots (P ++ Q) hs
  simp only [List.length_append] at hp
  simp only [bitAdd, appendWithCost_eq ]
  apply (Nat.add_le_add_left hp P.length).trans
  rw [hlenP, hlenQ]
  unfold denseAddCost
  ring_nf
  omega

end BitCounts

section EncodedBounds

variable {D : ℕ} {C : Type*}

theorem encodeProgramList_keys (P : CoeffList D C) (hP : ∀ p ∈ P, Retained D p.1) :
    ∀ a ∈ encodeProgramList P, a.1.length ≤ indexBits D := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact retained_index_bits p.1 (hP p hp)

theorem encodeSlots_keys (slots : List (RawIndex D)) (hs : ∀ a ∈ slots, Retained D a) :
    ∀ a ∈ slots.map encodeIndex, a.length ≤ indexBits D := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact retained_index_bits p (hs p hp)

theorem bitMul_encoded_cost (ops : RingProgram C) {q : ℕ} (budget : ProgramBudget ops q)
    (slots : List (RawIndex D)) (P Q : CoeffList D C)
    (hs : ∀ a ∈ slots, Retained D a)
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ a ∈ Q, Retained D a.1)
    (hlenP : P.length = slots.length) (hlenQ : Q.length = slots.length)
    (hslots : slots.length = slotCount D) :
    (bitMul ops (slots.map encodeIndex) (encodeProgramList P) (encodeProgramList Q)).2 ≤
      ((q + 6 * indexBits D + 5) * listFactor D) * monomialCount D ^ 4 := by
  apply (bitMul_cost ops budget _ _ _ (encodeSlots_keys slots hs)
    (encodeProgramList_keys P hP) (encodeProgramList_keys Q hQ)
    (by simpa using hlenP) (by simpa using hlenQ)).trans
  simp only [List.length_map, hslots]
  exact weighted_dense_events_uniform D _

/-- An absolute polynomial, including concrete binary coefficient arithmetic
and bitwise exponent comparisons/additions. List administration still uses
source events; this is not a primitive-machine trace theorem. -/
theorem bitEventFactor_degree (D h b : ℕ) :
    quarticEventBudget D b + 6 * indexBits D + 5 ≤
      9964 * parameterSize D h b ^ 4 := by
  have hq := quarticEventBudget_degree D h b
  have hi := indexBits_degree D h b
  have hS : 1 ≤ parameterSize D h b := by unfold parameterSize; omega
  have hp : parameterSize D h b ^ 2 ≤ parameterSize D h b ^ 4 :=
    Nat.pow_le_pow_right hS (by decide)
  have hpos : 1 ≤ parameterSize D h b ^ 4 := Nat.one_le_pow _ _ hS
  omega

end EncodedBounds

section DecodedBitLists

variable {D : ℕ} {C R : Type*} [CommRing R] (ops : RepresentedRing C R)

def bitDecodeList (P : BitCoeffList C) : BitCoeffList R :=
  P.map fun p => (p.1, ops.decode p.2)

@[simp] theorem bitDecodeList_encode (P : CoeffList D C) :
    bitDecodeList ops (encodeProgramList P) = encodeProgramList (decodeList ops P) := by
  simp only [bitDecodeList, encodeProgramList, decodeList, List.map_map, Function.comp_def]

theorem bitProject_decode (slots : List (RawIndex D)) (P : CoeffList D C) :
    bitDecodeList ops
        (bitProject ops.program (slots.map encodeIndex) (encodeProgramList P)).1 =
      encodeProgramList (project slots (decodeList ops P)) := by
  rw [bitProject_correct, bitDecodeList_encode, programProject_represented,
    representedProject_correct]

theorem bitAdd_decode (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    bitDecodeList ops
        (bitAdd ops.program (slots.map encodeIndex) (encodeProgramList P) (encodeProgramList Q)).1 =
      encodeProgramList (denseAdd slots (decodeList ops P) (decodeList ops Q)) := by
  rw [bitAdd_correct, bitDecodeList_encode, programAdd_represented, representedAdd_correct]

theorem bitMul_decode (slots : List (RawIndex D)) (P Q : CoeffList D C) :
    bitDecodeList ops
        (bitMul ops.program (slots.map encodeIndex) (encodeProgramList P) (encodeProgramList Q)).1 =
      encodeProgramList (denseMul slots (decodeList ops P) (decodeList ops Q)) := by
  rw [bitMul_correct, bitDecodeList_encode, programMul_represented, representedMul_correct]

end DecodedBitLists

section ConcreteBitLists

open SubexponentialSAT.SubexpQuarticRing

/-- The cost bound depends only on the actual callbacks. In particular it
does not need any semantic hypothesis on the cached reduction or constants. -/
theorem preparedProgram_budget (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t z o : QuarticCode p D) :
    ProgramBudget (preparedProgram p D M t z o)
      (quarticEventBudget D (Nat.log 2 p + 1)) := by
  constructor
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · intro a b
    apply (SubexpPreparedQuartic.binaryAdd_cost p (D + 1) M a b).trans
    change 4 * scalarBudget p (D + 1) ≤ 49 * scalarBudget p (D + 1)
    omega
  · exact SubexpPreparedQuartic.binaryMul_cost p (D + 1) M t
  · intro a
    apply (SubexpPreparedQuartic.binaryNeg_cost p (D + 1) M a).trans
    change 4 * scalarBudget p (D + 1) ≤ 49 * scalarBudget p (D + 1)
    omega

theorem prepared_bitMul_uniform (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t z o : QuarticCode p D)
    (slots : List (RawIndex D)) (P Q : CoeffList D (QuarticCode p D))
    (hs : ∀ a ∈ slots, Retained D a)
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ a ∈ Q, Retained D a.1)
    (hlenP : P.length = slots.length) (hlenQ : Q.length = slots.length)
    (hslots : slots.length = slotCount D) :
    (bitMul (preparedProgram p D M t z o) (slots.map encodeIndex)
        (encodeProgramList P) (encodeProgramList Q)).2 ≤
      (99640 * parameterSize D 4 (Nat.log 2 p + 1) ^ 10) * monomialCount D ^ 4 := by
  apply (bitMul_cost _ (preparedProgram_budget p D M t z o) _ _ _
    (encodeSlots_keys slots hs) (encodeProgramList_keys P hP) (encodeProgramList_keys Q hQ)
    (by simpa using hlenP) (by simpa using hlenQ)).trans
  simp only [List.length_map, hslots]
  exact weighted_dense_events_degree D 4 (Nat.log 2 p + 1) _ 9964 4
    (bitEventFactor_degree D 4 (Nat.log 2 p + 1))

end ConcreteBitLists

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpPreparedQuartic

/-- Data retained between calls to the scalar binary routines. -/
structure QuarticInitialization (p D : ℕ) where
  modulus : Modulus p (D + 1)
  reduction : QuarticCode p D
  zero : QuarticCode p D
  one : QuarticCode p D

def QuarticInitialization.program {p D : ℕ} [Fact p.Prime]
    (data : QuarticInitialization p D) : RingProgram (QuarticCode p D) :=
  preparedProgram p D data.modulus data.reduction data.zero data.one

/-- Setup uses binary multiplication for the prime power, binary negation for
the reduction data, and explicit bit copying/padding for the two constants. -/
def initializeQuartic (p D : ℕ) [Fact p.Prime] (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) (coefficients : QuarticCode p D) :
    QuarticInitialization p D × ℕ :=
  let M := prepareModulus p (D + 1) primeBits hvalue hwidth
  let t := prepareReduction p (D + 1) M.1 coefficients
  let z := prepareZero p (D + 1)
  let o := prepareOne p (D + 1)
  (⟨M.1, t.1, z.1, o.1⟩, M.2 + t.2 + z.2 + o.2)

noncomputable def initializedRing (p D : ℕ) [Fact p.Prime] (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) (coefficients : QuarticCode p D)
    (c : Fin 4 → ZMod (p ^ (D + 1)))
    (hc : coefficients.map (wordValue p (D + 1)) = Quad.ofFn c) :
    RepresentedRing (QuarticCode p D) (LiftRing.Extension (QuarticSearch.poly c)) :=
  let M := (prepareModulus p (D + 1) primeBits hvalue hwidth).1
  preparedRing p D M c (prepareReduction p (D + 1) M coefficients).1
    (prepareZero p (D + 1)).1 (prepareOne p (D + 1)).1
    (prepareReduction_correct p (D + 1) M c coefficients hc)
    (prepareZero_quotient p (D + 1) c)
    (prepareOne_quotient p (D + 1) (Nat.zero_lt_succ D) c)

@[simp] theorem initializedRing_program (p D : ℕ) [Fact p.Prime] (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) (coefficients : QuarticCode p D)
    (c : Fin 4 → ZMod (p ^ (D + 1)))
    (hc : coefficients.map (wordValue p (D + 1)) = Quad.ofFn c) :
    (initializedRing p D primeBits hvalue hwidth coefficients c hc).program =
      (initializeQuartic p D primeBits hvalue hwidth coefficients).1.program := rfl

theorem initializedRing_budget (p D : ℕ) [Fact p.Prime] (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) (coefficients : QuarticCode p D)
    (c : Fin 4 → ZMod (p ^ (D + 1)))
    (hc : coefficients.map (wordValue p (D + 1)) = Quad.ofFn c) :
    ScalarBudget (initializedRing p D primeBits hvalue hwidth coefficients c hc)
      (quarticEventBudget D (Nat.log 2 p + 1)) := by
  unfold initializedRing
  exact preparedRing_budget p D _ c _ _ _
    (prepareReduction_correct p (D + 1) _ c coefficients hc)
    (prepareZero_quotient p (D + 1) c)
    (prepareOne_quotient p (D + 1) (Nat.zero_lt_succ D) c)

theorem initializeQuartic_cost (p D : ℕ) [Fact p.Prime] (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) (coefficients : QuarticCode p D) :
    (initializeQuartic p D primeBits hvalue hwidth coefficients).2 ≤
      100 * (D + 2)^2 * (Nat.log 2 p + 2)^2 +
        4 * baseEventBudget D (Nat.log 2 p + 1) +
        24 * ((D + 1) * (Nat.log 2 p + 1)) + 8 := by
  have hm := prepareModulus_cost_quadratic p (D + 1) primeBits hvalue hwidth
  have ht := prepareReduction_cost p (D + 1)
    (prepareModulus p (D + 1) primeBits hvalue hwidth).1 coefficients
  have hz := prepareZero_cost p (D + 1)
  have ho := prepareOne_cost p (D + 1)
  rw [hwidth] at hm
  simp only [Nat.add_assoc] at hm
  norm_num only at hm
  change (initializeQuartic p D primeBits hvalue hwidth coefficients).2 ≤
    100 * (D + 2)^2 * (Nat.log 2 p + 2)^2 +
      4 * scalarBudget p (D + 1) + 24 * baseWidth p (D + 1) + 8
  simp only [initializeQuartic ]
  omega

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

open SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpLiftRing

/-- Fixed-width words are already their own executable bit representation. -/
def wordBlockCode (B : ℕ) (hB : 0 < B) : StackEncoding.BlockCode (Word B) where
  width := B
  width_pos := hB
  block := Subtype.val
  length_block := Subtype.property
  injective_block := Subtype.val_injective

def quadToPair {C : Type*} (a : Quad C) : (C × C) × (C × C) :=
  ((a.c0, a.c1), (a.c2, a.c3))

theorem quadToPair_injective {C : Type*} : Function.Injective (@quadToPair C) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- The actual raw coefficient payload has exactly four binary words. -/
def quarticCodeBlockCode (p D : ℕ) : StackEncoding.BlockCode (QuarticCode p D) :=
  let word := wordBlockCode (baseWidth p (D + 1))
    (Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
  let pair := recordBlockCode word word
  let four := recordBlockCode pair pair
  { width := four.width
    width_pos := four.width_pos
    block := fun a => four.block (quadToPair a)
    length_block := fun a => four.length_block (quadToPair a)
    injective_block := four.injective_block.comp quadToPair_injective }

@[simp] theorem quarticCodeBlockCode_width (p D : ℕ) :
    (quarticCodeBlockCode p D).width = coefficientBits D 4 (Nat.log 2 p + 1) := by
  simp only [quarticCodeBlockCode, recordBlockCode, wordBlockCode, coefficientBits, baseWidth]
  ring

def encodedCoefficientBlockCode (p D : ℕ) :
    StackEncoding.BlockCode (RetainedKey D × QuarticCode p D) :=
  recordBlockCode (keyBlockCode D) (quarticCodeBlockCode p D)

@[simp] theorem encodedCoefficientBlockCode_width (p D : ℕ) :
    (encodedCoefficientBlockCode p D).width = slotBits D 4 (Nat.log 2 p + 1) := by
  simp only [encodedCoefficientBlockCode, recordBlockCode, keyBlockCode,
    quarticCodeBlockCode_width, slotBits]

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

open SubexponentialSAT.SymbolicCost
open scoped BigOperators

theorem unaryWords_length_exact (xs : List ℕ) :
    (unaryWords xs).length = xs.sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [unaryWords, List.flatMap_cons, List.length_append, unaryWord,
      List.length_replicate, List.sum_cons, List.length_cons] at *
    simp only [List.length_nil] at *
    omega

theorem encodeIndex_length_exact {D : ℕ} (a : RawIndex D) :
    (encodeIndex a).length = (∑ i, a.1 i) + a.2.1 + a.2.2 + (D + 2) := by
  rw [encodeIndex, unaryWords_length_exact, length_indexData]
  simp [indexData, List.sum_ofFn, Nat.add_assoc]

theorem retained_sum_key_length {D : ℕ} (a b : RawIndex D)
    (ha : Retained D a) (hb : Retained D b) :
    (encodeIndex (a + b)).length ≤ indexBits D := by
  rw [encodeIndex_length_exact]
  change (∑ i, (a.1 i + b.1 i)) + (a.2.1 + b.2.1) +
    (a.2.2 + b.2.2) + (D + 2) ≤ _
  rw [Finset.sum_add_distrib]
  have ht : (∑ i, a.1 i) + (∑ i, b.1 i) + (a.2.1 + b.2.1) +
      (a.2.2 + b.2.2) + (D + 2) ≤ 9 * D + 2 := by
    obtain ⟨hax, hau, haz⟩ := ha
    obtain ⟨hbx, hbu, hbz⟩ := hb
    omega
  apply ht.trans
  unfold indexBits
  rcases (by omega : D = 0 ∨ D = 1 ∨ 2 ≤ D) with h | h | h
  · subst D; decide
  · subst D; decide
  · have hm := Nat.mul_le_mul_left D h
    nlinarith

theorem addIndexBits_suffix (as bs : List ℕ) (hlen : as.length = bs.length)
    (xs ys : List Bool) :
    (addIndexBits (unaryWords as ++ xs) (unaryWords bs ++ ys)).1 =
      unaryWords (List.zipWith (· + ·) as bs) ++ (addIndexBits xs ys).1 := by
  induction as generalizing bs with
  | nil =>
    have hb : bs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst bs
    simp [unaryWords]
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have ht : as.length = bs.length := Nat.succ.inj hlen
      change (addIndexBits ((unaryWord a ++ unaryWords as) ++ xs)
        ((unaryWord b ++ unaryWords bs) ++ ys)).1 =
          (unaryWord (a+b) ++ unaryWords (List.zipWith (· + ·) as bs)) ++ _
      rw [List.append_assoc, List.append_assoc, addIndexBits_prefix, ih bs ht]
      simp only [List.append_assoc]

theorem addIndexBits_zeroes (m n : ℕ) :
    (addIndexBits (List.replicate m false) (List.replicate n false)).1 =
      List.replicate (min m n) false := by
  induction m generalizing n with
  | zero => simp [addIndexBits]
  | succ m ih =>
    cases n with
    | zero => simp [List.replicate_succ, addIndexBits]
    | succ n => simp [List.replicate_succ, addIndexBits, ih, Nat.succ_min_succ]

def normalizeKey (width : ℕ) (bits : List Bool) : List Bool :=
  (bits ++ List.replicate width false).take width

theorem normalizeKey_eq (width : ℕ) (bits : List Bool) :
    normalizeKey width bits =
      bits.take width ++ List.replicate (width - bits.length) false := by
  simp only [normalizeKey, List.take_append, List.take_replicate]
  rw [Nat.min_eq_left (Nat.sub_le _ _)]

theorem normalizeKey_suffix (width : ℕ) (bits : List Bool) (m : ℕ)
    (hlen : bits.length ≤ width) :
    normalizeKey width (bits ++ List.replicate m false) =
      bits ++ List.replicate (width - bits.length) false := by
  simp only [normalizeKey, List.append_assoc, ← List.replicate_add, List.take_append,
    List.take_replicate, List.take_of_length_le hlen]
  rw [Nat.min_eq_left (by omega)]

theorem fixedKey_add_correct {D : ℕ} (a b : RawIndex D)
    (ha : Retained D a) (hb : Retained D b) :
    normalizeKey (indexBits D) (addIndexBits (fixedKey a) (fixedKey b)).1 =
      fixedKey (a + b) := by
  unfold fixedKey
  change normalizeKey (indexBits D)
    (addIndexBits (unaryWords (indexData a) ++ _)
      (unaryWords (indexData b) ++ _)).1 = _
  rw [addIndexBits_suffix _ _ (by simp), ← indexData_add, addIndexBits_zeroes]
  exact normalizeKey_suffix _ (encodeIndex (a + b)) _ (retained_sum_key_length a b ha hb)

end SubexponentialSAT.SubexpSymbolicCost
namespace SubexponentialSAT.SubexpSymbolicCost

variable {C R S : Type*} [CommRing R] [CommRing S]

/-- Postcompose only the mathematical decoder. Every executable callback,
including its returned cost, remains literally unchanged. -/
def RepresentedRing.map (ops : RepresentedRing C R) (f : R →+* S) : RepresentedRing C S where
  decode a := f (ops.decode a)
  zeroRun := ops.zeroRun
  oneRun := ops.oneRun
  addRun := ops.addRun
  mulRun := ops.mulRun
  negRun := ops.negRun
  zero_correct := by rw [ops.zero_correct, map_zero]
  one_correct := by rw [ops.one_correct, map_one]
  add_correct a b := by rw [ops.add_correct, map_add]
  mul_correct a b := by rw [ops.mul_correct, map_mul]
  neg_correct a := by rw [ops.neg_correct, map_neg]

@[simp] theorem RepresentedRing.program_map (ops : RepresentedRing C R) (f : R →+* S) :
    (ops.map f).program = ops.program := rfl

theorem ScalarBudget.map {ops : RepresentedRing C R} {q : ℕ}
    (budget : ScalarBudget ops q) (f : R →+* S) : ScalarBudget (ops.map f) q :=
  ⟨budget.zero, budget.one, budget.add, budget.mul, budget.neg⟩

end SubexponentialSAT.SubexpSymbolicCost

end OAI.Algorithms
