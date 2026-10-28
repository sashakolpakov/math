import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpDecodeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial

namespace OAI.Algorithms

/-!
# Runtime extraction of the constant coefficient word

The wire format is a framed list of polynomial coefficients, in increasing
degree order.  Each coefficient is a framed list of its four little-endian
base-ring words.  A fixed program selects the first record twice, restores the
word order, clears its work stacks, and preserves the modulus on stack five.

The input representation is an explicit boundary: this module does not assert
that an arithmetic callback returning a Lean list has already serialized it.
-/

namespace SubexponentialSAT.SubexpCountExtraction

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 8 7

private theorem state_ext {a b : Data} (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) :
    a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

def resetRegs (r : Fin 8 → Bool) : Fin 8 → Bool := readRegs r 0 1 none

abbrev atom (a : StructuredProgram.Atom 8 7) : Cmd 8 7 := .base (.atom a)

def afterPop (d : Data) (src : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks src).head?,
    Function.update d.stacks src (d.stacks src).tail⟩

theorem pop_eval (d : Data) (src : Fin 7) :
    Eval (atom (.pop src 0 1)) 1 d (afterPop d src) := by
  have h : (StructuredProgram.Atom.pop src 0 1).eval d = afterPop d src := rfl
  rw [← h]
  exact .base (.atom _ _)

def readerPorts (src dst : Fin 7) (hne : src ≠ dst) : RecordPrograms.Ports 8 7 where
  tag := 0
  present := 1
  found := 2
  source := src
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := hne

abbrev parseFrame (src dst : Fin 7) (hne : src ≠ dst) : Cmd 8 7 :=
  RecordPrograms.reader (readerPorts src dst hne)

def afterFrame (d : Data) (src dst : Fin 7) (bits rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst (bits.reverse ++ d.stacks dst)⟩

theorem parseFrame_eval (d : Data) (src dst : Fin 7) (hne : src ≠ dst)
    (bits rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (parseFrame src dst hne) (6 * bits.length + 4) d
      (afterFrame d src dst bits rest) := by
  let p := readerPorts src dst hne
  have hi : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ rest) (d.stacks dst) = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hin rfl
  have hf : RecordPrograms.state p d false true (d.regs 2)
      rest (bits.reverse ++ d.stacks dst) = afterFrame d src dst bits rest := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [RecordPrograms.state, afterFrame, readRegs, p, readerPorts]
    · rfl
  have h := RecordPrograms.reader_eval p d bits rest (d.stacks dst)
    (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hi, hf] at h
  exact h

def afterClear (d : Data) (src : Fin 7) : Data :=
  ⟨resetRegs d.regs, StackRoutines.clearStacks src d.stacks⟩

abbrev clear (src : Fin 7) : Cmd 8 7 :=
  .call (StackRoutines.clearProgram src 0 1)

theorem clear_eval (d : Data) (src : Fin 7) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (afterClear d src) := by
  exact .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

def afterTransfer (d : Data) (src dst : Fin 7) : Data :=
  ⟨resetRegs d.regs, StackRoutines.transferStacks src dst d.stacks⟩

abbrev transfer (src dst : Fin 7) : Cmd 8 7 :=
  .call (StackRoutines.transferProgram src dst 0 1)

theorem transfer_eval (d : Data) (src dst : Fin 7) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer d src dst) := by
  exact .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

/-- Select one list record, discard the rest, and restore its original order. -/
abbrev headCmd (src tmp dst : Fin 7) (hst : src ≠ tmp) : Cmd 8 7 :=
  .seq (atom (.pop src 0 1))
    (.ite 0 (.seq (parseFrame src tmp hst) (.seq (clear src) (transfer tmp dst))) (clear src))

def headResult (d : Data) (src dst : Fin 7) (bits : List Bool) : Data :=
  ⟨resetRegs d.regs, Function.update (Function.update d.stacks src []) dst bits⟩

theorem head_nonempty_eval (d : Data) (src tmp dst : Fin 7)
    (hst : src ≠ tmp) (hsd : src ≠ dst) (htd : tmp ≠ dst)
    (bits rest : List Bool)
    (hin : d.stacks src = true :: (Encoding.frame bits ++ rest))
    (htmp : d.stacks tmp = []) (hdst : d.stacks dst = []) :
    Eval (headCmd src tmp dst hst) (9 * bits.length + 2 * rest.length + 12)
      d (headResult d src dst bits) := by
  let d₁ := afterPop d src
  let d₂ := afterFrame d₁ src tmp bits rest
  let d₃ := afterClear d₂ src
  let d₄ := afterTransfer d₃ tmp dst
  have htag : d₁.regs 0 = true := by simp [d₁, afterPop, readRegs, hin]
  have hinput : d₁.stacks src = Encoding.frame bits ++ rest := by
    simp [d₁, afterPop, hin]
  have hrest : d₂.stacks src = rest := by
    simp [d₂, afterFrame, hst]
  have hword : d₃.stacks tmp = bits.reverse := by
    simp [d₃, d₂, d₁, afterClear, afterFrame, afterPop, StackRoutines.clearStacks,
      Ne.symm hst, htmp]
  have hf : d₄ = headResult d src dst bits := by
    apply state_ext
    · simp only [d₄, d₃, d₂, d₁, afterTransfer, afterClear, afterFrame, afterPop,
        headResult, resetRegs, StackRoutines.readRegs_reset]
    · funext j
      by_cases hjs : j = src <;> by_cases hjt : j = tmp <;> by_cases hjd : j = dst <;>
        simp_all [d₄, d₃, d₂, d₁, afterTransfer, afterClear, afterFrame, afterPop,
          headResult, StackRoutines.transferStacks, StackRoutines.clearStacks, Ne.symm hst, Ne.symm hsd, Ne.symm htd]
  have hp := pop_eval d src
  have hr := parseFrame_eval d₁ src tmp hst bits rest hinput
  have hc := clear_eval d₂ src
  rw [hrest] at hc
  have ht := transfer_eval d₃ tmp dst htd
  rw [hword, List.length_reverse] at ht
  have h : Eval (headCmd src tmp dst hst)
    (1 + ((6 * bits.length + 4 + (2 * rest.length + 3 + (3 * bits.length + 3))) + 1))
    d d₄ := Eval.seq hp (Eval.ite_true htag (Eval.seq hr (Eval.seq hc ht)))
  rw [hf] at h
  convert h using 1
  omega

theorem head_empty_eval (d : Data) (src tmp dst : Fin 7)
    (hst : src ≠ tmp) (hsd : src ≠ dst)
    (hin : d.stacks src = [false] ∨ d.stacks src = [])
    (hdst : d.stacks dst = []) :
    Eval (headCmd src tmp dst hst) 5 d (headResult d src dst []) := by
  let d₁ := afterPop d src
  have htag : d₁.regs 0 = false := by
    rcases hin with h | h <;> simp [d₁, afterPop, readRegs, h]
  have hrest : d₁.stacks src = [] := by
    rcases hin with h | h <;> simp [d₁, afterPop, h]
  have hf : afterClear d₁ src = headResult d src dst [] := by
    apply state_ext
    · simp only [d₁, afterClear, afterPop, headResult, resetRegs, StackRoutines.readRegs_reset]
    · funext j
      by_cases hjs : j = src <;> by_cases hjd : j = dst <;>
        simp_all [d₁, afterClear, afterPop, headResult, StackRoutines.clearStacks
          ]
  have hc := clear_eval d₁ src
  rw [hrest] at hc
  have h : Eval (headCmd src tmp dst hst) 5 d (afterClear d₁ src) :=
    Eval.seq (pop_eval d src) (Eval.ite_false htag hc)
  rwa [hf] at h

def headCost : ProgramEncoding.Records → ℕ
  | [] => 5
  | bits :: rest => 9 * bits.length + 2 * (ProgramEncoding.encodeRecords rest).length + 12

/-- A semantic description of the result is justified by an actual parser trace. -/
theorem head_records_eval (d : Data) (src tmp dst : Fin 7)
    (hst : src ≠ tmp) (hsd : src ≠ dst) (htd : tmp ≠ dst)
    (records : ProgramEncoding.Records)
    (hin : d.stacks src = ProgramEncoding.encodeRecords records)
    (htmp : d.stacks tmp = []) (hdst : d.stacks dst = []) :
    Eval (headCmd src tmp dst hst) (headCost records) d
      (headResult d src dst (records.headD [])) := by
  cases records with
  | nil => exact head_empty_eval d src tmp dst hst hsd (Or.inl hin) hdst
  | cons bits rest =>
      exact head_nonempty_eval d src tmp dst hst hsd htd bits
        (ProgramEncoding.encodeRecords rest) hin htmp hdst

theorem headCost_le (records : ProgramEncoding.Records) :
    headCost records ≤ 12 * ((ProgramEncoding.encodeRecords records).length + 1) := by
  cases records with
  | nil => decide
  | cons bits rest =>
      simp only [headCost, ProgramEncoding.encodeRecords, Encoding.length_encodeList_cons, id_eq]
      omega

abbrev Code (width : ℕ) := SubexpQuarticRing.Quad (SubexpQuarticRing.Word width)

def wordRecords {width : ℕ} (a : Code width) : ProgramEncoding.Records :=
  [a.c0.val, a.c1.val, a.c2.val, a.c3.val]

def encodeQuadWords {width : ℕ} (a : Code width) : List Bool :=
  ProgramEncoding.encodeRecords (wordRecords a)

def encodePolynomial {width : ℕ} (P : List (Code width)) : List Bool :=
  ProgramEncoding.encodeRecords (P.map encodeQuadWords)

def firstRecord {width : ℕ} : List (Code width) → List Bool
  | [] => []
  | a :: _ => encodeQuadWords a

def firstWord {width : ℕ} : List (Code width) → List Bool
  | [] => []
  | a :: _ => a.c0.val

def store (input record modulus word : List Bool) : Fin 7 → List Bool :=
  ![input, [], record, [], [], modulus, word]

def start (regs : Fin 8 → Bool) (modulus input : List Bool) : Data :=
  ⟨regs, store input [] modulus []⟩

def middle (regs : Fin 8 → Bool) (modulus record : List Bool) : Data :=
  ⟨resetRegs regs, store [] record modulus []⟩

def finish (regs : Fin 8 → Bool) (modulus word : List Bool) : Data :=
  ⟨resetRegs regs, store [] [] modulus word⟩

abbrev extractCmd : Cmd 8 7 :=
  .seq (headCmd 0 1 2 (by decide)) (headCmd 2 1 6 (by decide))

def innerCost {width : ℕ} : List (Code width) → ℕ
  | [] => 5
  | a :: _ => headCost (wordRecords a)

def extractionCost {width : ℕ} (P : List (Code width)) : ℕ :=
  headCost (P.map encodeQuadWords) + innerCost P

private theorem first_head_result {width : ℕ} (P : List (Code width))
    (regs : Fin 8 → Bool) (modulus : List Bool) :
    headResult (start regs modulus (encodePolynomial P)) 0 2
      ((P.map encodeQuadWords).headD []) = middle regs modulus (firstRecord P) := by
  apply state_ext
  · rfl
  · funext j
    cases P <;> fin_cases j <;> rfl

private theorem second_head_result {width : ℕ} (P : List (Code width))
    (regs : Fin 8 → Bool) (modulus : List Bool) :
    headResult (middle regs modulus (firstRecord P)) 2 6 (firstWord P) =
      finish regs modulus (firstWord P) := by
  apply state_ext
  · simp only [headResult, middle, finish, resetRegs, StackRoutines.readRegs_reset]
  · funext j
    fin_cases j <;> rfl

theorem extract_eval {width : ℕ} (P : List (Code width))
    (regs : Fin 8 → Bool) (modulus : List Bool) :
    Eval extractCmd (extractionCost P) (start regs modulus (encodePolynomial P))
      (finish regs modulus (firstWord P)) := by
  have h₀ := head_records_eval (start regs modulus (encodePolynomial P))
    0 1 2 (by decide) (by decide) (by decide) (P.map encodeQuadWords) rfl rfl rfl
  rw [first_head_result] at h₀
  have h₁ : Eval (headCmd 2 1 6 (by decide))
      (innerCost P)
      (middle regs modulus (firstRecord P))
      (finish regs modulus (firstWord P)) := by
    cases P with
    | nil =>
        have h := head_empty_eval (middle regs modulus (firstRecord ([] : List (Code width))))
          2 1 6 (by decide) (by decide) (Or.inr rfl) rfl
        change Eval (headCmd 2 1 6 (by decide)) 5
          (middle regs modulus (firstRecord ([] : List (Code width))))
          (headResult (middle regs modulus (firstRecord ([] : List (Code width)))) 2 6
            (firstWord ([] : List (Code width)))) at h
        rwa [second_head_result] at h
    | cons a P =>
        have h := head_records_eval (middle regs modulus (firstRecord (a :: P)))
          2 1 6 (by decide) (by decide) (by decide) (wordRecords a) rfl rfl rfl
        change Eval (headCmd 2 1 6 (by decide)) (headCost (wordRecords a))
          (middle regs modulus (firstRecord (a :: P)))
          (headResult (middle regs modulus (firstRecord (a :: P))) 2 6 (firstWord (a :: P))) at h
        rwa [second_head_result] at h
  exact Eval.seq h₀ h₁

theorem firstRecord_length_le {width : ℕ} (P : List (Code width)) :
    (firstRecord P).length ≤ (encodePolynomial P).length := by
  cases P with
  | nil => simp [firstRecord]
  | cons a P =>
      simp only [firstRecord, encodePolynomial, List.map_cons,
        ProgramEncoding.encodeRecords, Encoding.length_encodeList_cons, id_eq]
      omega

theorem extractionCost_le {width : ℕ} (P : List (Code width)) :
    extractionCost P ≤ 24 * ((encodePolynomial P).length + 1) := by
  have h₀ := headCost_le (P.map encodeQuadWords)
  have hlen := firstRecord_length_le P
  cases P with
  | nil => simp [extractionCost, innerCost, headCost, encodePolynomial, ProgramEncoding.encodeRecords,
      Encoding.encodeList]
  | cons a P =>
      have h₁ := headCost_le (wordRecords a)
      change headCost ((a :: P).map encodeQuadWords) ≤
        12 * ((encodePolynomial (a :: P)).length + 1) at h₀
      change (encodeQuadWords a).length ≤ (encodePolynomial (a :: P)).length at hlen
      change headCost (wordRecords a) ≤ 12 * ((encodeQuadWords a).length + 1) at h₁
      change headCost ((a :: P).map encodeQuadWords) + headCost (wordRecords a) ≤ _
      omega

/-- This fixed 39-label table operates on arbitrarily long encoded coefficient lists. -/
abbrev program : Program 8 7 39 := compiled extractCmd 0 6

theorem run {width : ℕ} (P : List (Code width))
    (regs : Fin 8 → Bool) (modulus : List Bool) :
    RunsIn program (25 * ((encodePolynomial P).length + 1))
      ((start regs modulus (encodePolynomial P)).withPC (some program.entry))
      ((finish regs modulus (firstWord P)).withPC none) := by
  refine ⟨extractionCost P + 1, ?_, compiled_halt_trace (extract_eval P regs modulus) 0 6⟩
  have h := extractionCost_le P
  omega

theorem run_preserves_modulus {width : ℕ} (P : List (Code width))
    (regs : Fin 8 → Bool) (modulus : List Bool) :
    (finish regs modulus (firstWord P)).stacks 5 = modulus := rfl

theorem encodeQuadWords_length {width : ℕ} (a : Code width) :
    (encodeQuadWords a).length = 8 * width + 9 := by
  simp only [encodeQuadWords, ProgramEncoding.encodeRecords_length, wordRecords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, a.c0.property, a.c1.property, a.c2.property, a.c3.property]
  omega

theorem encodePolynomial_length {width : ℕ} (P : List (Code width)) :
    (encodePolynomial P).length = (16 * width + 20) * P.length + 1 := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      change (ProgramEncoding.encodeRecords (encodeQuadWords a :: P.map encodeQuadWords)).length = _
      rw [ProgramEncoding.encodeRecords, Encoding.length_encodeList_cons]
      change 2 * (encodeQuadWords a).length + 2 + (encodePolynomial P).length = _
      rw [encodeQuadWords_length, ih, List.length_cons]
      ring

theorem firstWord_length_le_width {width : ℕ} (P : List (Code width)) :
    (firstWord P).length ≤ width := by
  cases P with
  | nil => exact Nat.zero_le _
  | cons a P => exact a.c0.property.le

theorem firstWord_length_le_encoded {width : ℕ} (P : List (Code width)) :
    (firstWord P).length ≤ (encodePolynomial P).length := by
  cases P with
  | nil => exact Nat.zero_le _
  | cons a P =>
      have h := firstRecord_length_le (a :: P)
      change (encodeQuadWords a).length ≤ (encodePolynomial (a :: P)).length at h
      rw [encodeQuadWords_length] at h
      change a.c0.val.length ≤ _
      rw [a.c0.property]
      omega

section Semantics

open SubexpQuarticRing SubexpLiftRing BinaryArithmetic

variable (p μ : ℕ) [Fact p.Prime]

noncomputable def decodeCode (c : Fin 4 → ZMod (p ^ μ))
    (a : Code (baseWidth p μ)) : LiftRing.Extension (QuarticSearch.poly c) :=
  quotientDenote c (a.map (wordValue p μ))

def zeroCode : Code (baseWidth p μ) :=
  ⟨SubexpPreparedQuartic.zeroWord p μ, SubexpPreparedQuartic.zeroWord p μ,
    SubexpPreparedQuartic.zeroWord p μ, SubexpPreparedQuartic.zeroWord p μ⟩

omit [Fact (Nat.Prime p)] in
theorem zeroCode_decode (c : Fin 4 → ZMod (p ^ μ)) :
    decodeCode p μ c (zeroCode p μ) = 0 := by
  simp only [decodeCode, zeroCode, Quad.map, SubexpPreparedQuartic.zeroWord_value]
  rw [quotientDenote_const, map_zero]

omit [Fact (Nat.Prime p)] in
/-- The only arithmetic selection step: a dense polynomial's zeroth
  coefficient is the decoded head, with a proved encoded zero for an empty list. -/
theorem firstCode_of_denote_eq (c : Fin 4 → ZMod (p ^ μ))
    (P : List (Code (baseWidth p μ)))
    (H : Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (hH : PolynomialAlgorithm.denote (P.map (decodeCode p μ c)) = H) :
    decodeCode p μ c (P.headD (zeroCode p μ)) = H.coeff 0 := by
  have h := congrArg (fun f => Polynomial.coeff f 0) hH
  cases P with
  | nil =>
      simpa only [List.map_nil, PolynomialAlgorithm.denote_nil, Polynomial.coeff_zero,
        List.headD_nil, zeroCode_decode] using h
  | cons a P =>
      simpa only [List.map_cons, PolynomialAlgorithm.coeff_denote,
        PolynomialAlgorithm.coeff, List.headD_cons] using h

omit [Fact p.Prime] in
private theorem zeroWord_toNat :
    BinaryArithmetic.toNat (SubexpPreparedQuartic.zeroWord p μ).val = 0 := by
  have h (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, toNat_cons, bitVal_false, ih]
  exact h _

omit [Fact (Nat.Prime p)] in
theorem firstWord_toNat_eq_head (P : List (Code (baseWidth p μ))) :
    BinaryArithmetic.toNat (firstWord P) = BinaryArithmetic.toNat (P.headD (zeroCode p μ)).c0.val := by
  cases P with
  | nil => exact (zeroWord_toNat p μ).symm
  | cons a P => rfl

theorem firstWord_mod_eq (hμ : 0 < μ) (c : Fin 4 → ZMod (p ^ μ))
    (P : List (Code (baseWidth p μ)))
    (H : Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (hH : PolynomialAlgorithm.denote (P.map (decodeCode p μ c)) = H)
    (count : ℕ) (hcount : count < p ^ μ)
    (hvalue : H.coeff 0 = (count : LiftRing.Extension (QuarticSearch.poly c))) :
    BinaryArithmetic.toNat (firstWord P) % p ^ μ = count := by
  rw [firstWord_toNat_eq_head]
  exact SubexpDecodedCount.first_mod_eq p μ hμ c (P.headD (zeroCode p μ)) count hcount
    ((firstCode_of_denote_eq p μ c P H hH).trans hvalue)

theorem decoded_answer_iff (hμ : 0 < μ) (c : Fin 4 → ZMod (p ^ μ))
    (P : List (Code (baseWidth p μ)))
    (H : Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (hH : PolynomialAlgorithm.denote (P.map (decodeCode p μ c)) = H)
    (modulus : List Bool) (hmod : BinaryArithmetic.toNat modulus = p ^ μ)
    (count : ℕ) (hcount : count < p ^ μ)
    (hvalue : H.coeff 0 = (count : LiftRing.Extension (QuarticSearch.poly c))) :
    SubexpDecodeProgram.answer modulus (firstWord P) = true ↔ 0 < count := by
  have hm : 0 < BinaryArithmetic.toNat modulus := by
    rw [hmod]
    exact pow_pos (Fact.out : p.Prime).pos μ
  rw [SubexpDecodeProgram.answer_iff _ _ hm, hmod,
    firstWord_mod_eq p μ hμ c P H hH count hcount hvalue]

end Semantics

/-! ## Link the actual parser to the actual remainder-and-positivity program -/

abbrev decisionProgram : Program 8 7 135 :=
  ProgramLinking.link program SubexpDecodeProgram.program

def decisionBudget (modulus input : List Bool) : ℕ :=
  25 * (input.length + 1) + 105 * (modulus.length + input.length + 1) ^ 2

def decisionOutput (modulus word : List Bool) : List Bool :=
  SubexpDecodeProgram.answer modulus word ::
    PositiveWordProgram.residual (ModularArithmetic.reduce modulus word)

theorem decision_run {width : ℕ} (P : List (Code width))
    (regs : Fin 8 → Bool) (modulus : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn decisionProgram (decisionBudget modulus (encodePolynomial P))
        ((start regs modulus (encodePolynomial P)).withPC (some decisionProgram.entry))
        ⟨none, finalRegs,
          ModularDivisionPrograms.resting (decisionOutput modulus (firstWord P)) modulus []⟩ := by
  have h₀ := run P regs modulus
  change RunsIn program (25 * ((encodePolynomial P).length + 1))
    ⟨some program.entry, regs, ModularDivisionPrograms.resting (encodePolynomial P) modulus []⟩
    ⟨none, resetRegs regs, ModularDivisionPrograms.resting [] modulus (firstWord P)⟩ at h₀
  obtain ⟨finalRegs, h₁⟩ := SubexpDecodeProgram.run (resetRegs regs) modulus (firstWord P)
  have h := ProgramLinking.link_runsIn program SubexpDecodeProgram.program h₀ rfl h₁
  have hlength := firstWord_length_le_encoded P
  have hbound :
      25 * ((encodePolynomial P).length + 1) +
        105 * (modulus.length + (firstWord P).length + 1) ^ 2 ≤
      decisionBudget modulus (encodePolynomial P) := by
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul_left 105 (Nat.pow_le_pow_left (by omega) 2)
  refine ⟨finalRegs, ?_⟩
  simpa only [decisionProgram, decisionBudget, decisionOutput, start, store,
    StructuredProgram.State.withPC, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    ProgramLinking.link, ProgramLinking.linkInto, ModularDivisionPrograms.resting,
    ModularDivisionPrograms.seven] using h.mono hbound

theorem decision_primitive_run {width : ℕ} (P : List (Code width))
    (regs : Fin 8 → Bool) (modulus : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      Computation.RunsIn (primitive decisionProgram).step
        (primitiveOverhead decisionProgram * decisionBudget modulus (encodePolynomial P))
        (primitiveCfg decisionProgram
          ((start regs modulus (encodePolynomial P)).withPC (some decisionProgram.entry)))
        (primitiveCfg decisionProgram ⟨none, finalRegs,
          ModularDivisionPrograms.resting (decisionOutput modulus (firstWord P)) modulus []⟩) := by
  obtain ⟨finalRegs, h⟩ := decision_run P regs modulus
  exact ⟨finalRegs, primitive_execution decisionProgram h⟩

theorem decision_primitive_answer (regs : Fin 8 → Bool) (modulus word : List Bool) :
    (primitiveCfg decisionProgram ⟨none, regs,
      ModularDivisionPrograms.resting (decisionOutput modulus word) modulus []⟩).state =
        .inl (SubexpDecodeProgram.answer modulus word) := by
  apply StackCompiler.compiled_terminal
  rfl

/-- All semantic premises concern the represented polynomial returned by CRT;
the transition from its encoded list to the answer is an actual finite program. -/
theorem count_decision_run (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (c : Fin 4 → ZMod (p ^ μ)) (P : List (Code (SubexpLiftRing.baseWidth p μ)))
    (H : Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (hH : PolynomialAlgorithm.denote (P.map (decodeCode p μ c)) = H)
    (regs : Fin 8 → Bool) (modulus : List Bool)
    (hmod : BinaryArithmetic.toNat modulus = p ^ μ)
    (count : ℕ) (hcount : count < p ^ μ)
    (hvalue : H.coeff 0 = (count : LiftRing.Extension (QuarticSearch.poly c))) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn decisionProgram (decisionBudget modulus (encodePolynomial P))
        ((start regs modulus (encodePolynomial P)).withPC (some decisionProgram.entry))
        ⟨none, finalRegs,
          ModularDivisionPrograms.resting (decisionOutput modulus (firstWord P)) modulus []⟩ ∧
      ((decisionOutput modulus (firstWord P)).head? = some true ↔ 0 < count) := by
  obtain ⟨finalRegs, hrun⟩ := decision_run P regs modulus
  refine ⟨finalRegs, hrun, ?_⟩
  simpa only [decisionOutput, List.head?_cons, Option.some.injEq] using
    decoded_answer_iff p μ hμ c P H hH modulus hmod count hcount hvalue

/-- The compiled primitive tape machine reaches the correct Boolean answer
from the explicitly encoded polynomial and prepared modulus. -/
theorem count_primitive_decision (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (c : Fin 4 → ZMod (p ^ μ)) (P : List (Code (SubexpLiftRing.baseWidth p μ)))
    (H : Polynomial (LiftRing.Extension (QuarticSearch.poly c)))
    (hH : PolynomialAlgorithm.denote (P.map (decodeCode p μ c)) = H)
    (regs : Fin 8 → Bool) (modulus : List Bool)
    (hmod : BinaryArithmetic.toNat modulus = p ^ μ)
    (count : ℕ) (hcount : count < p ^ μ)
    (hvalue : H.coeff 0 = (count : LiftRing.Extension (QuarticSearch.poly c))) :
    ∃ final : (primitive decisionProgram).Cfg,
      Computation.RunsIn (primitive decisionProgram).step
        (primitiveOverhead decisionProgram * decisionBudget modulus (encodePolynomial P))
        (primitiveCfg decisionProgram
          ((start regs modulus (encodePolynomial P)).withPC (some decisionProgram.entry))) final ∧
      (final.state = .inl true ↔ 0 < count) := by
  obtain ⟨finalRegs, hrun⟩ := decision_primitive_run P regs modulus
  refine ⟨_, hrun, ?_⟩
  rw [decision_primitive_answer, Sum.inl.injEq]
  exact decoded_answer_iff p μ hμ c P H hH modulus hmod count hcount hvalue

end SubexponentialSAT.SubexpCountExtraction

end OAI.Algorithms
