import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentLoopProof

namespace OAI.Algorithms

/-! The bit program's record stream is the serialized raw incidence argument,
with records reversed because the machine prepends each emitted term. -/

namespace SubexponentialSAT.SubexpArgumentEmitLoop

open SubexpArgumentCode

abbrev Bits := List Bool

def columnBodies (B i j : ℕ) (u : Bool) : List Bits → List Bits
  | [] => []
  | c :: cs => SubexpArgumentProgram.recordBody
      (SubexpArgumentKeyEmitter.paddedKey i cs.length j B true u) c ::
      columnBodies B (i+1) j u cs

def rowBodies (B j : ℕ) (u : Bool) : List (List Bits) → List Bits
  | [] => []
  | cs :: rss => columnBodies B 0 j u cs ++ rowBodies B (j+1) false rss

def argumentBodies (D B : ℕ) (beta negBeta : Bits) (rss : List (List Bits)) : List Bits :=
  SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey D 0 0 B false false) beta ::
  SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey D 0 0 B false true) negBeta ::
  rowBodies B 0 true rss

theorem columnOutput_encode (cs : List Bits) (B i j : ℕ) (u : Bool) (prior : List Bits) :
    columnOutput B i j u cs (Encoding.encodeList id prior) =
      Encoding.encodeList id ((columnBodies B i j u cs).reverse ++ prior) := by
  induction cs generalizing i prior with
  | nil => rfl
  | cons c cs ih =>
    simpa [columnOutput, columnBodies, prepend, Encoding.encodeList,
      List.reverse_cons, List.append_assoc] using
      ih (i+1) (SubexpArgumentProgram.recordBody
        (SubexpArgumentKeyEmitter.paddedKey i cs.length j B true u) c :: prior)

theorem rowsOutput_encode (rss : List (List Bits)) (B j : ℕ) (u : Bool) (prior : List Bits) :
    rowsOutput B j u rss (Encoding.encodeList id prior) =
      Encoding.encodeList id ((rowBodies B j u rss).reverse ++ prior) := by
  induction rss generalizing j u prior with
  | nil => rfl
  | cons cs rss ih =>
    rw [rowsOutput, columnOutput_encode, ih]
    simp only [rowBodies, List.reverse_append, List.append_assoc]

theorem argumentOutput_encode (D B : ℕ) (beta negBeta : Bits) (rss : List (List Bits)) :
    argumentOutput D B beta negBeta rss [false] =
      Encoding.encodeList id (argumentBodies D B beta negBeta rss).reverse := by
  have h := rowsOutput_encode rss B 0 true
    [SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey D 0 0 B false true) negBeta,
      SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey D 0 0 B false false) beta]
  simpa [argumentOutput, argumentBodies, prepend, Encoding.encodeList, List.reverse_cons,
    List.append_assoc] using h

theorem columnBodies_ofFn (n : ℕ) (f : Fin n → Bits) (B i j : ℕ) (u : Bool) :
    columnBodies B i j u (List.ofFn f) =
      List.ofFn (fun k : Fin n => SubexpArgumentProgram.recordBody
        (SubexpArgumentKeyEmitter.paddedKey (i + k.val) (n - k.val - 1) j B true u) (f k)) := by
  induction n generalizing i with
  | zero => simp [columnBodies]
  | succ n ih =>
    rw [List.ofFn_succ, columnBodies, List.ofFn_succ, ih]
    simp only [List.length_ofFn, Fin.val_zero, Fin.val_succ, Nat.add_zero,
      Nat.sub_zero, Nat.add_sub_cancel]
    congr 2
    funext k
    have hl : i + 1 + k.val = i + (k.val + 1) := by omega
    have hr : n - k.val - 1 = n + 1 - (k.val + 1) - 1 := by omega
    rw [hl, hr]

def serializeTerm {D : ℕ} {A : Type*} (encode : A → Bits)
    (term : SymbolicCost.RawIndex D × A) : Bits :=
  SubexpArgumentProgram.recordBody (SubexpSymbolicCost.fixedKey term.1) (encode term.2)

theorem columnBodies_rawRow {D : ℕ} {A : Type*} (encode : A → Bits)
    (f : Fin D → A) (j : ℕ) (u : Bool) :
    columnBodies (SubexpSymbolicCost.indexBits D) 0 j u (List.ofFn (fun i => encode (f i))) =
      (rawRow (if u then 1 else 0) j f).map (serializeTerm encode) := by
  rw [columnBodies_ofFn]
  simp only [rawRow, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [serializeTerm, SubexpArgumentKeyEmitter.paddedKey_coordinate]

theorem rowBodies_positive {D : ℕ} {A : Type*} (encode : A → Bits)
    (n j : ℕ) (a : Fin n → Fin D → A) :
    rowBodies (SubexpSymbolicCost.indexBits D) j false
      (List.ofFn (fun k => List.ofFn (fun i => encode (a k i)))) =
      ((List.ofFn (fun k : Fin n => rawRow 0 (j+k.val) (a k))).flatten).map (serializeTerm encode) := by
  induction n generalizing j with
  | zero => simp [rowBodies]
  | succ n ih =>
    rw [List.ofFn_succ, rowBodies, columnBodies_rawRow, ih, List.ofFn_succ]
    simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_zero, Nat.add_zero,
      List.flatten_cons, List.map_append]
    congr 1
    apply congrArg (List.map (serializeTerm encode))
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext k
    simp only [Fin.val_succ]
    congr 1
    omega

theorem argumentBodies_compileArgument {D q : ℕ} {A : Type*} [Neg A]
    (encode : A → Bits) (beta : A) (a : Fin (q+1) → Fin D → A) :
    argumentBodies D (SubexpSymbolicCost.indexBits D) (encode beta) (encode (-beta))
      (List.ofFn (fun j => List.ofFn (fun i => encode (a j i)))) =
      (compileArgument beta a).map (serializeTerm encode) := by
  rw [List.ofFn_succ]
  simp only [argumentBodies, rowBodies, columnBodies_rawRow, rowBodies_positive,
    ↓reduceIte, SubexpArgumentKeyEmitter.paddedKey_constant]
  simp only [compileArgument, List.map_append, List.map_cons, serializeTerm,
    List.cons_append, List.nil_append]
  congr 3
  apply congrArg (List.map (serializeTerm encode))
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  congr 1
  omega

/-- The exact serialized result of the fixed-control incidence-argument program. -/
theorem argumentOutput_compileArgument {D q : ℕ} {A : Type*} [Neg A]
    (encode : A → Bits) (beta : A) (a : Fin (q+1) → Fin D → A) :
    argumentOutput D (SubexpSymbolicCost.indexBits D) (encode beta) (encode (-beta))
      (List.ofFn (fun j => List.ofFn (fun i => encode (a j i)))) [false] =
      Encoding.encodeList (serializeTerm encode) (compileArgument beta a).reverse := by
  rw [argumentOutput_encode, argumentBodies_compileArgument, ← List.map_reverse]
  induction (compileArgument beta a).reverse with
  | nil => rfl
  | cons t ts ih => simp [Encoding.encodeList, ih]

/-- The actual fixed program produces the encoded raw compiler output from
coefficient records. Its input order is beta, negative beta, then row-major
Taylor coefficients. All dimension and degree controls are runtime words. -/
theorem compileArgument_trace {D q : ℕ} {A : Type*} [Neg A]
    (encode : A → Bits) (beta : A) (a : Fin (q+1) → Fin D → A)
    (v p mark priorU saved : Bool) (tail : Bits) :
    BitProgram.Trace program
      (argumentCost D (SubexpSymbolicCost.indexBits D) (encode beta) (encode (-beta))
        (List.ofFn (fun j => List.ofFn (fun i => encode (a j i)))) + 1)
      ((ready v p mark priorU saved
        (Encoding.frame (encode beta) ++ (Encoding.frame (encode (-beta)) ++
          (rowsFrames (List.ofFn (fun j => List.ofFn (fun i => encode (a j i)))) ++ tail)))
        [false] D (SubexpSymbolicCost.indexBits D) 0 0 0 0 (q+1)).withPC (some program.entry))
      ((ready false false true false saved tail
        (Encoding.encodeList (serializeTerm encode) (compileArgument beta a).reverse)
        D (SubexpSymbolicCost.indexBits D) 0 0 0 0 0).withPC none) := by
  let rss := List.ofFn (fun j => List.ofFn (fun i => encode (a j i)))
  have hrows : ∀ cs ∈ rss, cs.length = D := by
    intro cs hcs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hcs
    exact List.length_ofFn
  have hn : rss ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp [rss] at hl
  have h := program_trace rss hrows v p mark priorU saved (encode beta) (encode (-beta))
    tail [false] (SubexpSymbolicCost.indexBits D)
  simpa only [hn, ↓reduceIte, rss, List.length_ofFn, argumentOutput_compileArgument] using h

/-- Reversing the serialized raw terms changes no polynomial coefficient. -/
theorem denote_reversed_compileArgument {D q : ℕ} {A : Type*} [CommRing A]
    (beta : A) (a : Fin (q+1) → Fin D → A) :
    SymbolicCost.denote (compileArgument beta a).reverse = SymbolicCost.denote (compileArgument beta a) := by
  rw [denote_eq_sum, denote_eq_sum, List.map_reverse, List.sum_reverse]

theorem payloadBits_le (cs : List Bits) (W : ℕ) (h : ∀ c ∈ cs, c.length ≤ W) :
    payloadBits cs ≤ cs.length * W := by
  induction cs with
  | nil => simp [payloadBits]
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [payloadBits, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem rowsPayloadBits_le (rss : List (List Bits)) (D W : ℕ)
    (hrows : ∀ cs ∈ rss, cs.length = D)
    (hbits : ∀ cs ∈ rss, ∀ c ∈ cs, c.length ≤ W) :
    rowsPayloadBits rss ≤ rss.length * D * W := by
  induction rss with
  | nil => simp [rowsPayloadBits]
  | cons cs rss ih =>
    have hc := payloadBits_le cs W (hbits cs (by simp))
    rw [hrows cs (by simp)] at hc
    have ht := ih (fun ds hd => hrows ds (by simp [hd]))
      (fun ds hd => hbits ds (by simp [hd]))
    simp only [rowsPayloadBits, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

/-- A uniform bit-step bound with all growing parameters shown explicitly.
No unit-cost polynomial or coefficient oracle occurs in this statement. -/
theorem argumentCost_uniform (rss : List (List Bits)) (D B W : ℕ) (beta negBeta : Bits)
    (hrows : ∀ cs ∈ rss, cs.length = D)
    (hbits : ∀ cs ∈ rss, ∀ c ∈ cs, c.length ≤ W)
    (hb : beta.length ≤ W) (hn : negBeta.length ≤ W) :
    argumentCost D B beta negBeta rss + 1 ≤
      29 * (2 + rss.length * D) * W + 68 * D + 64 * B + 401 +
        rss.length * (D * (33 * (D + rss.length) + 32 * B + 224) + 23) := by
  have ht := argumentCost_le rss hrows B beta negBeta
  have hp := rowsPayloadBits_le rss D W hrows hbits
  nlinarith

/-- Raw argument keys use the total padding function. Even a key that will be
removed by projection is emitted completely; no retained-key premise is needed. -/
theorem coordinate_key_length_le {D : ℕ} (i : Fin D) (j q B : ℕ) (u : Bool) (hj : j ≤ q) :
    (SubexpArgumentKeyEmitter.paddedKey i.val (D-i.val-1) j B true u).length ≤
      max B (D + q + 4) := by
  have hi := i.isLt
  have hr : (SubexpArgumentKeyEmitter.rawKey i.val (D-i.val-1) j true u).length ≤ D+q+4 := by
    cases u <;> simp [SubexpArgumentKeyEmitter.rawKey, SubexpArgumentKeyEmitter.markBits,
      SubexpArgumentKeyEmitter.uBits] <;> omega
  have hB : B ≤ max B (D+q+4) := le_max_left _ _
  have hR := hr.trans (le_max_right B (D+q+4))
  simp only [SubexpArgumentKeyEmitter.paddedKey, List.length_append, List.length_replicate]
  omega

theorem constant_key_length_le (D j q B : ℕ) (u : Bool) (hj : j ≤ q) :
    (SubexpArgumentKeyEmitter.paddedKey D 0 j B false u).length ≤ max B (D+q+4) := by
  have hr : (SubexpArgumentKeyEmitter.rawKey D 0 j false u).length ≤ D+q+4 := by
    cases u <;> simp [SubexpArgumentKeyEmitter.rawKey, SubexpArgumentKeyEmitter.markBits,
      SubexpArgumentKeyEmitter.uBits] <;> omega
  have hB : B ≤ max B (D+q+4) := le_max_left _ _
  have hR := hr.trans (le_max_right B (D+q+4))
  simp only [SubexpArgumentKeyEmitter.paddedKey, List.length_append, List.length_replicate]
  omega

end SubexponentialSAT.SubexpArgumentEmitLoop

end OAI.Algorithms
