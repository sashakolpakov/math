import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRecordScan
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram

namespace OAI.Algorithms

/-!
# A fixed bit program for one packing bucket

The input is a framed query followed by framed `(type key, vertex payload)`
records. The routine compares actual bit strings. It consumes all records,
keeps the query on port 2, and prepends matching framed payloads on port 5.
Supplying records in reverse vertex order produces the original bucket order.
-/

namespace SubexponentialSAT.Subexp.BucketProgram

open BitProgram StructuredProgram StructuredCalls SubexpRecordScan

private theorem states_eq {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

private theorem cfgs_eq {r s l : ℕ} {a b : BitProgram.Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hp
  cases hr
  cases hs
  rfl

abbrev Record := List Bool × List Bool

def encodeRecords : List Record → List Bool
  | [] => []
  | (key, payload) :: rs => Encoding.frame key ++ (Encoding.frame payload ++ encodeRecords rs)

def frames : List (List Bool) → List Bool
  | [] => []
  | x :: xs => Encoding.frame x ++ frames xs

def selected : List Record → List Bool → List (List Bool)
  | [], _ => []
  | (key, payload) :: rs, query =>
    if key = query then payload :: selected rs query else selected rs query

theorem frames_append (xs ys : List (List Bool)) :
    frames (xs ++ ys) = frames xs ++ frames ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [frames, ih, List.append_assoc]

theorem selected_append (xs ys : List Record) (query : List Bool) :
    selected (xs ++ ys) query = selected xs query ++ selected ys query := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨key, payload⟩
    by_cases h : key = query <;> simp [selected, h, ih]

theorem selected_reverse (rs : List Record) (query : List Bool) :
    selected rs.reverse query = (selected rs query).reverse := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨key, payload⟩
    by_cases h : key = query <;>
      simp [List.reverse_cons, selected_append, selected, h, ih]

def scanOutput (rs : List Record) (query output : List Bool) : List Bool :=
  frames (selected rs query).reverse ++ output

theorem scanOutput_cons (key payload : List Bool) (rs : List Record)
    (query output : List Bool) :
    scanOutput ((key, payload) :: rs) query output =
      scanOutput rs query (if key = query then Encoding.frame payload ++ output else output) := by
  by_cases h : key = query <;>
    simp [scanOutput, selected, h, frames_append, frames, List.append_assoc]

theorem scanOutput_reverse (rs : List Record) (query output : List Bool) :
    scanOutput rs.reverse query output = frames (selected rs query) ++ output := by
  simp [scanOutput, selected_reverse]

abbrev peekInput : StructuredCalls.Cmd 5 6 := .base (.atom (.peek 0 0 1))
abbrev loopBody : StructuredCalls.Cmd 5 6 := .seq oneRecord peekInput
abbrev scanLoop : StructuredCalls.Cmd 5 6 := .while 1 loopBody
abbrev scan : StructuredCalls.Cmd 5 6 := .seq peekInput scanLoop
abbrev command : StructuredCalls.Cmd 5 6 := .seq (.call (parseFrame 0 2)) scan
def program := StructuredCalls.compiled command 0 5

theorem command_control_size : StructuredCalls.size command = 69 := by decide

def ready (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) : Data :=
  recordState (readRegs regs 0 1 (encodeRecords rs).head?)
    (encodeRecords rs) [] query.reverse [] [] output

theorem peekInput_eval (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    StructuredCalls.Eval peekInput 1
      (recordState regs (encodeRecords rs) [] query.reverse [] [] output)
      (ready regs rs query output) := by
  exact StructuredCalls.Eval.base (StructuredProgram.Eval.atom _ _)

theorem ready_guard_nil (regs : Fin 5 → Bool) (query output : List Bool) :
    (ready regs [] query output).regs 1 = false := by
  simp [ready, encodeRecords, recordState, readRegs]

theorem ready_guard_cons (regs : Fin 5 → Bool) (key payload : List Bool)
    (rs : List Record) (query output : List Bool) :
    (ready regs ((key, payload) :: rs) query output).regs 1 = true := by
  cases key <;> simp [ready, encodeRecords, recordState, readRegs, Encoding.frame]

def loopBudget : List Record → List Bool → ℕ
  | [], _ => 1
  | (key, payload) :: rs, query => recordCost key query payload + 2 + loopBudget rs query

/-- An actual structured execution of the EOF-controlled loop. -/
theorem scanLoop_eval (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    ∃ n ≤ loopBudget rs query, ∃ regs',
      StructuredCalls.Eval scanLoop n (ready regs rs query output)
        (recordState regs' [] [] query.reverse [] [] (scanOutput rs query output)) := by
  induction rs generalizing regs output with
  | nil =>
    refine ⟨1, le_rfl, (ready regs [] query output).regs, ?_⟩
    simpa [scanLoop, ready, encodeRecords, scanOutput, selected, frames] using
      (StructuredCalls.Eval.while_false (test := (1 : Fin 5)) (body := loopBody)
        (ready_guard_nil regs query output))
  | cons row rs ih =>
    rcases row with ⟨key, payload⟩
    let rr := (ready regs ((key, payload) :: rs) query output).regs
    let out := if key = query then Encoding.frame payload ++ output else output
    obtain ⟨nr, hnr, regs₁, he⟩ :=
      oneRecord_eval rr key query payload (encodeRecords rs) output
    have hrecord : StructuredCalls.Eval oneRecord nr
        (ready regs ((key, payload) :: rs) query output)
        (recordState regs₁ (encodeRecords rs) [] query.reverse [] [] out) := by
      simpa only [ready, encodeRecords, rr, out] using he.1
    have hpeek := peekInput_eval regs₁ rs query out
    obtain ⟨nt, hnt, regs₂, ht⟩ := ih regs₁ out
    have hbody : StructuredCalls.Eval loopBody (nr + 1)
        (ready regs ((key, payload) :: rs) query output) (ready regs₁ rs query out) :=
      StructuredCalls.Eval.seq hrecord hpeek
    have hw := StructuredCalls.Eval.while_true
      (ready_guard_cons regs key payload rs query output) hbody ht
    refine ⟨(nr + 1) + nt + 1, ?_, regs₂, ?_⟩
    · simp only [loopBudget]
      omega
    · simpa only [scanLoop, scanOutput_cons, out] using hw

theorem scan_eval (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    ∃ n ≤ 1 + loopBudget rs query, ∃ regs',
      StructuredCalls.Eval scan n
        (recordState regs (encodeRecords rs) [] query.reverse [] [] output)
        (recordState regs' [] [] query.reverse [] [] (scanOutput rs query output)) := by
  obtain ⟨n, hn, regs', he⟩ := scanLoop_eval regs rs query output
  exact ⟨1 + n, Nat.add_le_add_left hn 1, regs',
    StructuredCalls.Eval.seq (peekInput_eval regs rs query output) he⟩

/-- Parse the query once, then run the fixed record loop. -/
theorem command_eval (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    ∃ n ≤ 6 * query.length + 5 + loopBudget rs query, ∃ regs',
      StructuredCalls.Eval command n
        (recordState regs (Encoding.frame query ++ encodeRecords rs) [] [] [] [] output)
        (recordState regs' [] [] query.reverse [] [] (scanOutput rs query output)) := by
  let regs₁ := readRegs regs 0 1 (some false)
  have hp : StructuredCalls.Eval (.call (parseFrame 0 2)) (6 * query.length + 4)
      (recordState regs (Encoding.frame query ++ encodeRecords rs) [] [] [] [] output)
      (recordState regs₁ (encodeRecords rs) [] query.reverse [] [] output) := by
    have h := parseFrame_eval
      (recordState regs (Encoding.frame query ++ encodeRecords rs) [] [] [] [] output)
      0 2 (by decide) query (encodeRecords rs) rfl
    convert h using 1
    apply states_eq
    · rfl
    · funext j
      fin_cases j <;> simp [afterFrame, storage]
  obtain ⟨n, hn, regs', he⟩ := scan_eval regs₁ rs query output
  refine ⟨(6 * query.length + 4) + n, by omega, regs', ?_⟩
  exact StructuredCalls.Eval.seq hp he

/-- This is a trace of the actual fixed instruction table, including its halt. -/
theorem program_trace (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    ∃ n ≤ 6 * query.length + 6 + loopBudget rs query, ∃ regs',
      Trace program n
        ((recordState regs (Encoding.frame query ++ encodeRecords rs) [] [] [] [] output).withPC
          (some program.entry))
        ((recordState regs' [] [] query.reverse [] [] (scanOutput rs query output)).withPC none) := by
  obtain ⟨n, hn, regs', he⟩ := command_eval regs rs query output
  exact ⟨n + 1, by omega, regs', StructuredCalls.compiled_halt_trace he 0 5⟩

theorem record_count_le_length (rs : List Record) : rs.length ≤ (encodeRecords rs).length := by
  induction rs with
  | nil => simp [encodeRecords]
  | cons row rs ih =>
    rcases row with ⟨key, payload⟩
    simp only [encodeRecords, List.length_append, Encoding.length_frame, List.length_cons]
    omega

theorem encodeRecords_length_le (rs : List Record) (K B : ℕ)
    (hkey : ∀ row ∈ rs, row.1.length ≤ K)
    (hpayload : ∀ row ∈ rs, row.2.length ≤ B) :
    (encodeRecords rs).length ≤ rs.length * (2 * K + 2 * B + 2) := by
  induction rs with
  | nil => simp [encodeRecords]
  | cons row rs ih =>
    rcases row with ⟨key, payload⟩
    have hk := hkey (key, payload) (by simp)
    have hp := hpayload (key, payload) (by simp)
    have ht := ih (fun row hr => hkey row (List.mem_cons_of_mem _ hr))
      (fun row hr => hpayload row (List.mem_cons_of_mem _ hr))
    simp only [encodeRecords, List.length_append, Encoding.length_frame, List.length_cons]
    simp only at hk hp
    nlinarith

theorem loopBudget_le (rs : List Record) (query : List Bool) :
    loopBudget rs query ≤ 9 * (encodeRecords rs).length +
      rs.length * (9 * query.length + 20) + 1 := by
  induction rs with
  | nil => simp [loopBudget, encodeRecords]
  | cons row rs ih =>
    rcases row with ⟨key, payload⟩
    simp only [loopBudget, encodeRecords, List.length_append, Encoding.length_frame,
      List.length_cons, recordCost]
    nlinarith

/-- Polynomial bound in encoded data lengths, derived from the measured loop. -/
theorem traceBudget_le (rs : List Record) (query : List Bool) :
    6 * query.length + 6 + loopBudget rs query ≤
      40 * ((encodeRecords rs).length + 1) * (query.length + 1) := by
  have hl := loopBudget_le rs query
  have hc := Nat.mul_le_mul_right (9 * query.length + 20) (record_count_le_length rs)
  nlinarith

theorem program_primitive (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (40 * ((encodeRecords rs).length + 1) * (query.length + 1)))
      (BitProgram.primitiveCfg program
        ((recordState regs (Encoding.frame query ++ encodeRecords rs) [] [] [] [] output).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((recordState regs' [] [] query.reverse [] [] (scanOutput rs query output)).withPC none)) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs rs query output
  exact ⟨regs', BitProgram.primitive_execution program
    ⟨n, hn.trans (traceBudget_le rs query), ht⟩⟩

/-- Reversing the serialized record order makes the bucket output preserve
the original vertex order. The full frame of every selected index is emitted. -/
theorem ordered_bucket_trace (regs : Fin 5 → Bool) (rs : List Record)
    (query output : List Bool) :
    ∃ n ≤ 40 * ((encodeRecords rs.reverse).length + 1) * (query.length + 1), ∃ regs',
      Trace program n
        ((recordState regs (Encoding.frame query ++ encodeRecords rs.reverse) [] [] [] [] output).withPC
          (some program.entry))
        ((recordState regs' [] [] query.reverse [] []
          (frames (selected rs query) ++ output)).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs rs.reverse query output
  refine ⟨n, hn.trans (traceBudget_le rs.reverse query), regs', ?_⟩
  simpa only [scanOutput_reverse] using ht

theorem initial_eq (input : List Bool) :
    BitProgram.initial program input =
      (recordState (fun _ => false) input [] [] [] [] []).withPC (some program.entry) := by
  apply cfgs_eq
  · rfl
  · rfl
  · funext j
    fin_cases j <;> rfl

/-- A raw-input trace: the query is supplied as the first frame on the input
stack, and all work stacks start empty. -/
theorem initial_ordered_trace (rs : List Record) (query : List Bool) :
    ∃ n ≤ 40 * ((encodeRecords rs.reverse).length + 1) * (query.length + 1), ∃ regs',
      Trace program n
        (BitProgram.initial program (Encoding.frame query ++ encodeRecords rs.reverse))
        ((recordState regs' [] [] query.reverse [] []
          (frames (selected rs query))).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := ordered_bucket_trace (fun _ => false) rs query []
  refine ⟨n, hn, regs', ?_⟩
  rw [initial_eq]
  simpa only [List.append_nil] using ht

theorem initial_ordered_primitive (rs : List Record) (query : List Bool) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (40 * ((encodeRecords rs.reverse).length + 1) * (query.length + 1)))
      (BitProgram.primitiveCfg program
        (BitProgram.initial program (Encoding.frame query ++ encodeRecords rs.reverse)))
      (BitProgram.primitiveCfg program
        ((recordState regs' [] [] query.reverse [] []
          (frames (selected rs query))).withPC none)) := by
  obtain ⟨n, hn, regs', ht⟩ := initial_ordered_trace rs query
  exact ⟨regs', BitProgram.primitive_execution program ⟨n, hn, ht⟩⟩

section TypedBucket

variable {V U : Type*} [DecidableEq U]

def vertexRecords (vertices : List V) (label : V → U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool) : List Record :=
  vertices.map fun v => (encodeType (label v), encodeVertex v)

theorem selected_vertexRecords (vertices : List V) (label : V → U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (u : U) :
    selected (vertexRecords vertices label encodeType encodeVertex) (encodeType u) =
      (vertices.filter (fun v => decide (label v = u))).map encodeVertex := by
  induction vertices with
  | nil => rfl
  | cons v vs ih =>
    dsimp only [vertexRecords] at ih
    by_cases h : label v = u <;>
      simp [vertexRecords, selected, hinj.eq_iff, h, ih]

/-- The encoded output agrees exactly with the executable constructive bucket. -/
theorem constructive_bucket_output (P : ConstructivePacking.PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (u : U) :
    selected (vertexRecords P.vertices.values P.label encodeType encodeVertex) (encodeType u) =
      (P.bucket u).map encodeVertex :=
  selected_vertexRecords P.vertices.values P.label encodeType encodeVertex hinj u

/-- The fixed bit program computes precisely the typed constructive bucket
when its records contain injectively encoded type keys. -/
theorem constructive_bucket_trace (P : ConstructivePacking.PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (u : U) :
    let rs := vertexRecords P.vertices.values P.label encodeType encodeVertex
    ∃ n ≤ 40 * ((encodeRecords rs.reverse).length + 1) * ((encodeType u).length + 1),
      ∃ regs', Trace program n
        (BitProgram.initial program (Encoding.frame (encodeType u) ++ encodeRecords rs.reverse))
        ((recordState regs' [] [] (encodeType u).reverse [] []
          (frames ((P.bucket u).map encodeVertex))).withPC none) := by
  dsimp only
  simpa only [constructive_bucket_output P encodeType encodeVertex hinj u] using
    initial_ordered_trace (vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (encodeType u)

end TypedBucket

section UniversalBucket

variable {D r Q Δ : ℕ}

/-- Concrete records use the existing fixed-width universal-type encoding
and framed unary vertex indices. -/
def universalRows
    (P : ConstructivePacking.PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) :
    List Record :=
  vertexRecords P.vertices.values P.label CollisionProgram.encodeType
    (fun v => Encoding.encodeNat v.val)

theorem universalRows_length_bound
    (P : ConstructivePacking.PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) :
    (encodeRecords (universalRows P).reverse).length ≤
      D * (2 * CollisionProgram.typeWidth r Q Δ + 2 * D + 2) := by
  have hk : ∀ row ∈ (universalRows P).reverse,
      row.1.length ≤ CollisionProgram.typeWidth r Q Δ := by
    intro row hr
    have hm : row ∈ universalRows P := by simpa only [List.mem_reverse] using hr
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
    exact le_of_eq (CollisionProgram.encodeType_length (P.label v))
  have hp : ∀ row ∈ (universalRows P).reverse, row.2.length ≤ D := by
    intro row hr
    have hm : row ∈ universalRows P := by simpa only [List.mem_reverse] using hr
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
    simpa only [Encoding.length_encodeNat] using Nat.succ_le_of_lt v.isLt
  have hl : (universalRows P).reverse.length = D := by
    simp only [List.length_reverse, universalRows, vertexRecords, List.length_map,
      P.vertices.length_eq_card, Fintype.card_fin]
  simpa only [hl] using encodeRecords_length_le (universalRows P).reverse
    (CollisionProgram.typeWidth r Q Δ) D hk hp

def universalBudget (D r Q Δ : ℕ) : ℕ :=
  40 * (D * (2 * CollisionProgram.typeWidth r Q Δ + 2 * D + 2) + 1) *
    (CollisionProgram.typeWidth r Q Δ + 1)

/-- The actual fixed program computes a bucket of the universal-type labeling,
with a proved polynomial bound in the dimension and encoded type width. -/
theorem universal_bucket_trace
    (P : ConstructivePacking.PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (u : MulticolorTypes.UniversalType r Q Δ) :
    ∃ n ≤ universalBudget D r Q Δ, ∃ regs',
      Trace program n
        (BitProgram.initial program (Encoding.frame (CollisionProgram.encodeType u) ++
          encodeRecords (universalRows P).reverse))
        ((recordState regs' [] [] (CollisionProgram.encodeType u).reverse [] []
          (frames ((P.bucket u).map (fun v => Encoding.encodeNat v.val)))).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := constructive_bucket_trace P CollisionProgram.encodeType
    (fun v => Encoding.encodeNat v.val) CollisionProgram.encodeType_injective u
  have hbound := Nat.mul_le_mul_right (CollisionProgram.typeWidth r Q Δ + 1)
    (Nat.mul_le_mul_left 40 (Nat.add_le_add_right (universalRows_length_bound P) 1))
  have hn' : n ≤ 40 * ((encodeRecords (universalRows P).reverse).length + 1) *
      (CollisionProgram.typeWidth r Q Δ + 1) := by
    simpa only [universalRows, CollisionProgram.encodeType_length] using hn
  refine ⟨n, ?_, regs', ht⟩
  exact hn'.trans hbound

end UniversalBucket

end SubexponentialSAT.Subexp.BucketProgram

end OAI.Algorithms
