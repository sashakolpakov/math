import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableProgram

namespace OAI.Algorithms

/-! Measured execution of the fixed nested dense-row table producer.
The first boundary below completes the unary coordinate loop, including its
real initialization, record reversal, and counter cleanup. -/

namespace SubexponentialSAT.SubexpDenseRowTableProgram

open BitProgram StructuredCalls

def CoordinateReady (a : Data) (D : ℕ) : Prop :=
  a.stacks 264 = unary D ∧
    ∀ i ∈ ([87, 262, 263, 266, 267, 269, 270] : List (Fin 288)), a.stacks i = []

def coordinateWords (render : ℕ → Word) (D : ℕ) : List Word :=
  (List.range D).map render

def coordinateRunCost (render : ℕ → Word) (cost : ℕ → ℕ) (D : ℕ) : ℕ :=
  9 * D + 13 + coordinateBudget render cost 0 D +
    10 * (Encoding.encodeList id (coordinateWords render D).reverse).length

def coordinateResult (a : Data) (regs : Fin 25 → Bool)
    (render : ℕ → Word) (D : ℕ) : Data :=
  ⟨regs, Function.update a.stacks 267 (Encoding.encodeList id (coordinateWords render D))⟩

/-- Complete coordinate-list production. The input is a runtime dimension,
and each complete row is obtained by an actual invocation of the supplied
fixed row program. Only output267 changes among the stacks. -/
theorem coordinates_eval (row : Code) (render : ℕ → Word) (cost : ℕ → ℕ)
    (a : Data) (D : ℕ) (ha : CoordinateReady a D)
    (hrow : RowContract row render cost a D) :
    ∃ n ≤ coordinateRunCost render cost D, ∃ regs,
      Eval (coordinates row) n a (coordinateResult a regs render D) := by
  have h264 := ha.1
  have h87 : a.stacks 87 = [] := ha.2 _ (by simp)
  have h262 : a.stacks 262 = [] := ha.2 _ (by simp)
  have h263 : a.stacks 263 = [] := ha.2 _ (by simp)
  have h266 : a.stacks 266 = [] := ha.2 _ (by simp)
  have h267 : a.stacks 267 = [] := ha.2 _ (by simp)
  have h269 : a.stacks 269 = [] := ha.2 _ (by simp)
  have h270 : a.stacks 270 = [] := ha.2 _ (by simp)
  let c1 := copied 264 263 a
  let c2 := pushed 266 false c1
  have hc : Eval (copy 264 263) (7 * D + 5) a c1 := by
    simpa [h264, unary] using
      copy_eval 264 263 (by decide) (by decide) (by decide) a h270
  have hp : Eval (pushConstant 266 false) 2 c1 c2 := pushConstant_eval _ _ _
  have hstart : c2 = coordinateState a c2.regs 0 D [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h : i = 87
      · subst i; simp [c1, copied,
          StackRoutines.copyStacks, h87]
      by_cases h : i = 262
      · subst i; simp [c1, copied,
          StackRoutines.copyStacks, h262, unary]
      by_cases h : i = 263
      · subst i; simp [c1, copied,
          StackRoutines.copyStacks, h263, h264]
      by_cases h : i = 266
      · subst i; simp [c1, copied,
          StackRoutines.copyStacks, h266, Encoding.encodeList]
      simp_all [c2, c1, pushed, copied, StackRoutines.copyStacks]
  have hk := coordinatePeek_eval a c2.regs 0 D [] []
  rw [← hstart] at hk
  obtain ⟨n, hn, loopRegs, hl⟩ := coordinateLoop_eval row render cost a D hrow 0 D
    (by omega) [] c2.regs
  let records := (coordinateWords render D).reverse
  have hrecords : collectedRows render 0 D [] = records := by
    simp [collectedRows_eq, records, coordinateWords, ← List.range_eq_range']
  rw [hrecords, Nat.zero_add] at hl
  let c3 := coordinateState a loopRegs D 0 records []
  let c4 := cleared 262 c3
  let c5 := pushed 267 false c4
  have hz : Eval (clear 262) (2 * D + 3) c3 c4 := by
    simpa [c3, unary] using clear_eval 262 c3
  have hpush : Eval (pushConstant 267 false) 2 c4 c5 := pushConstant_eval _ _ _
  have hc5source : c5.stacks 266 = Encoding.encodeList id records ++ [] := by
    simp [c5, c4, c3, cleared, pushed, StackRoutines.clearStacks]
  have hc5target : c5.stacks 267 = Encoding.encodeList id ([] : List Word) := by
    simp [c5, c4, c3, cleared, pushed, coordinateState,
      StackRoutines.clearStacks, h267, Encoding.encodeList]
  have hc5work : c5.stacks 269 = [] := by
    simp [c5, c4, c3, cleared, pushed, coordinateState,
      StackRoutines.clearStacks, h269]
  obtain ⟨m, hm, hr⟩ := reverseRecords_eval 266 267 (by decide) (by decide)
    (by decide) (by decide) (by decide) c5 records [] [] hc5source hc5target hc5work
  let final := reversedRecords 266 267 records [] [] c5
  have hfinal : final = coordinateResult a final.regs render D := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h267i : i = 267
      · subst i; simp [records]
      by_cases h87i : i = 87
      · subst i; simp [c5, c4, c3, pushed, cleared,
          coordinateState, StackRoutines.clearStacks, h87]
      by_cases h262i : i = 262
      · subst i; simp [c5, c4, c3, pushed, cleared,
          coordinateState, StackRoutines.clearStacks, h262]
      by_cases h263i : i = 263
      · subst i; simp [c5, c4, c3, pushed, cleared,
          coordinateState, StackRoutines.clearStacks, h263, unary]
      by_cases h266i : i = 266
      · subst i; simp [c5, c4, c3, pushed, cleared,
          coordinateState, StackRoutines.clearStacks, h266]
      simp [c5, c4, c3, pushed, cleared,
        coordinateState, StackRoutines.clearStacks,
        h267i, h87i, h262i, h263i, h266i]
  have run := hc.seq (hp.seq (hk.seq (hl.seq (hz.seq (hpush.seq hr)))))
  refine ⟨(7 * D + 5) + (2 + (1 + (n + ((2 * D + 3) + (2 + m))))),
    ?_, final.regs, ?_⟩
  · dsimp [coordinateRunCost]
    change m ≤ 10 * (Encoding.encodeList id (coordinateWords render D).reverse).length at hm
    omega
  · change Eval (coordinates row) _ a final at run
    rw [hfinal] at run
    exact run

theorem coordinateResult_output (a : Data) (regs : Fin 25 → Bool)
    (render : ℕ → Word) (D : ℕ) :
    (coordinateResult a regs render D).stacks 267 =
      Encoding.encodeList id (coordinateWords render D) := by simp [coordinateResult]

theorem coordinateResult_frame (a : Data) (regs : Fin 25 → Bool)
    (render : ℕ → Word) (D : ℕ) (i : Fin 288) (hi : i ≠ 267) :
    (coordinateResult a regs render D).stacks i = a.stacks i := by
  simp [coordinateResult, hi]

def vertexReady (a : Data) (v : ℕ) : Data :=
  ⟨readRegs a.regs 0 1 (some false), Function.update a.stacks 260 (unary v)⟩

theorem vertexPop_eval (a : Data) (v : ℕ)
    (hv : a.stacks 260 = (Encoding.encodeNat v).reverse) :
    Eval (atom (.pop 260 0 1)) 1 a (vertexReady a v) := by
  have hbits : a.stacks 260 = false :: unary v := by
    simpa [Encoding.encodeNat, unary, List.reverse_append, List.reverse_replicate] using hv
  simpa [atom, vertexReady, hbits, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using
    Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 260 0 1) a)

def scopeReset (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 19 false) 20 true) 21 false,
    a.stacks⟩

theorem resetScope_eval (a : Data) : Eval resetScope 3 a (scopeReset a) := by
  let b : Data := (StructuredProgram.Atom.set 19 false).eval a
  let c : Data := (StructuredProgram.Atom.set 20 true).eval b
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 19 false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (20 : Fin 25) true) b)
  have h3 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (21 : Fin 25) false) c)
  simpa [b, c, resetScope, scopeReset, atom, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h1.seq (h2.seq h3)

def incidenceResult (a : Data) (regs : Fin 25 → Bool) (render : ℕ → Word) (D : ℕ) : Data :=
  ⟨regs, Function.update (Function.update a.stacks 260 []) 268
    (true :: (Encoding.frame (Encoding.encodeList id (coordinateWords render D)) ++
      a.stacks 268))⟩

def incidenceCost (render : ℕ → Word) (cost : ℕ → ℕ) (D v : ℕ) : ℕ :=
  coordinateRunCost render cost D +
    8 * (Encoding.encodeList id (coordinateWords render D)).length + 2 * v + 17

/-- One parsed scope occurrence produces all D complete rows and one outer
incidence record. Its input vertex is decoded by an actual pop; no ambient
coordinate list or polynomial-row list is supplied as input. -/
theorem incidenceCallback_eval (row : Code) (render : ℕ → Word) (cost : ℕ → ℕ)
    (a : Data) (D v : ℕ) (ha : CoordinateReady a D)
    (hv : a.stacks 260 = (Encoding.encodeNat v).reverse)
    (hrow : RowContract row render cost (vertexReady a v) D) :
    ∃ n ≤ incidenceCost render cost D v, ∃ regs,
      regs 19 = false ∧ regs 20 = true ∧ regs 21 = false ∧
      Eval (incidenceCallback row) n a (incidenceResult a regs render D) := by
  have ha' : CoordinateReady (vertexReady a v) D := by
    constructor
    · simpa [vertexReady] using ha.1
    · intro i hi
      have he := ha.2 i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [vertexReady] using he
  have h267 : a.stacks 267 = [] := ha.2 _ (by simp)
  have h269 : a.stacks 269 = [] := ha.2 _ (by simp)
  have hp := vertexPop_eval a v hv
  obtain ⟨n, hn, regs, hc⟩ := coordinates_eval row render cost (vertexReady a v) D ha' hrow
  let bits := Encoding.encodeList id (coordinateWords render D)
  let c1 := coordinateResult (vertexReady a v) regs render D
  let c2 := transferred 267 269 c1
  let c3 := emitted 269 268 bits c2
  let c4 := cleared 260 c3
  let c5 := scopeReset c4
  have ht : Eval (transfer 267 269) (3 * bits.length + 3) c1 c2 := by
    simpa [c2, c1, coordinateResult, bits] using transfer_eval 267 269 (by decide) c1
  have hbits : c2.stacks 269 = bits.reverse := by
    simp [c2, c1, transferred, StackRoutines.transferStacks, coordinateResult,
      vertexReady, h269, bits]
  have he : Eval (emit 269 268) (5 * bits.length + 7) c2 c3 :=
    emit_eval 269 268 (by decide) (by decide) (by decide) (by decide) (by decide) c2 bits hbits
  have hz : Eval (clear 260) (2 * v + 3) c3 c4 := by
    simpa [c4, c3, c2, c1, emitted, transferred, StackRoutines.transferStacks,
      coordinateResult, vertexReady, unary] using clear_eval 260 c3
  have hr : Eval resetScope 3 c4 c5 := resetScope_eval c4
  have hfinal : c5 = incidenceResult a c5.regs render D := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h : i = 268
      · subst i; simp [c4, c3, c2, c1, cleared, emitted,
          transferred, coordinateResult, vertexReady, StackRoutines.clearStacks,
          StackRoutines.transferStacks, bits]
      by_cases h : i = 260
      · subst i; simp [c4, cleared, StackRoutines.clearStacks]
      by_cases h : i = 267
      · subst i; simp [c4, c3, c2, cleared, emitted, transferred,
          StackRoutines.clearStacks, StackRoutines.transferStacks, h267]
      by_cases h : i = 269
      · subst i; simp [c4, c3, cleared, emitted,
          StackRoutines.clearStacks, h269]
      simp_all [c5, c4, c3, c2, c1, scopeReset, cleared, emitted, transferred,
        coordinateResult, vertexReady, StackRoutines.clearStacks,
        StackRoutines.transferStacks]
  refine ⟨1 + (n + ((3 * bits.length + 3) + ((5 * bits.length + 7) +
    ((2 * v + 3) + 3)))), ?_, c5.regs, ?_, ?_, ?_, ?_⟩
  · dsimp [incidenceCost]
    change n ≤ coordinateRunCost render cost D at hn
    dsimp [bits]
    omega
  · simp [c5, scopeReset]
  · simp [c5, scopeReset]
  · simp [c5, scopeReset]
  · have run := hp.seq (hc.seq (ht.seq (he.seq (hz.seq hr))))
    change Eval (incidenceCallback row) _ a c5 at run
    rw [hfinal] at run
    exact run

end SubexponentialSAT.SubexpDenseRowTableProgram


/-! The ordinary record parser executes each fixed callback in order. This
file records its exact state fold and measured parser/branch overhead; the
callback premises are traces of executable code in the same machine model. -/

namespace SubexponentialSAT.SubexpDenseRowTableProgram

open BitProgram StructuredCalls

abbrev Store := Fin 288 → Word

def foldStore {α : Type*} (stepStore : α → Store → Store) : Store → List α → Store
  | initial, [] => initial
  | initial, x :: xs => foldStore stepStore (stepStore x initial) xs

def foldBudget {α : Type*} (encode : α → Word) (stepStore : α → Store → Store)
    (cost : α → Store → ℕ) : Store → List α → ℕ
  | _, [] => 0
  | initial, x :: xs => 6 * (encode x).length + cost x initial + 7 +
      foldBudget encode stepStore cost (stepStore x initial) xs

/-- These premises contain executions of one fixed callback. They record
neither a semantic instruction nor a supplied list of output polynomials. -/
def FoldCalls {α : Type*} (ports : RecordPrograms.Ports 25 288) (callback : Code)
    (encode : α → Word) (stepStore : α → Store → Store) (cost : α → Store → ℕ) :
    Store → List α → Prop
  | _, [] => True
  | initial, x :: xs =>
      (∀ (regs : Fin 25 → Bool) (suffix : Word),
        ∃ n ≤ cost x initial, ∃ finalRegs,
          Eval callback n
            (RecordPrograms.state ports ⟨regs, initial⟩ false true false suffix (encode x).reverse)
            (RecordPrograms.state ports ⟨finalRegs, stepStore x initial⟩
              false true false suffix [])) ∧
      FoldCalls ports callback encode stepStore cost (stepStore x initial) xs

theorem fold_loop_eval {α : Type*} (ports : RecordPrograms.Ports 25 288) (callback : Code)
    (encode : α → Word) (stepStore : α → Store → Store) (cost : α → Store → ℕ)
    (values : List α) (initial : Store)
    (hc : FoldCalls ports callback encode stepStore cost initial values)
    (regs : Fin 25 → Bool) (suffix : Word) :
    ∃ n ≤ 1 + foldBudget encode stepStore cost initial values, ∃ finalRegs,
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports ⟨regs, initial⟩ (values.map encode) suffix)
        (RecordPrograms.state ports ⟨finalRegs, foldStore stepStore initial values⟩
          false true false suffix []) := by
  induction values generalizing initial regs with
  | nil =>
      refine ⟨1, by simp [foldBudget], regs, ?_⟩
      simpa [foldStore, RecordPrograms.afterTag] using
        Eval.while_false (body := RecordPrograms.body ports callback)
          (a := RecordPrograms.afterTag ports ⟨regs, initial⟩ [] suffix) (by
            simp [RecordPrograms.afterTag])
  | cons x xs ih =>
      rcases hc with ⟨hcall, hrest⟩
      let tail := Encoding.encodeList id (xs.map encode) ++ suffix
      obtain ⟨n, hn, middleRegs, hcallback⟩ := hcall regs tail
      obtain ⟨m, hm, finalRegs, htail⟩ := ih (stepStore x initial) hrest middleRegs
      have hreader : Eval (RecordPrograms.reader ports) (6 * (encode x).length + 4)
          (RecordPrograms.afterTag ports ⟨regs, initial⟩ ((x :: xs).map encode) suffix)
          (RecordPrograms.state ports ⟨regs, initial⟩ false true false tail (encode x).reverse) := by
        simpa [RecordPrograms.afterTag, tail] using
          RecordPrograms.reader_eval ports ⟨regs, initial⟩ (encode x) tail [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports ⟨middleRegs, stepStore x initial⟩
            false true false tail [])
          (RecordPrograms.afterTag ports ⟨middleRegs, stepStore x initial⟩
            (xs.map encode) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports ⟨middleRegs, stepStore x initial⟩
          (xs.map encode) suffix false true
      have hbody := hreader.seq (hcallback.seq hbranch)
      have run := Eval.while_true (body := RecordPrograms.body ports callback)
        (by simp [RecordPrograms.afterTag]) hbody htail
      refine ⟨(6 * (encode x).length + 4 + (n + 2)) + m + 1, ?_, finalRegs, ?_⟩
      · simp only [foldBudget]
        omega
      · simpa only [foldStore] using run

theorem encodeList_map_id {α : Type*} (encode : α → Word) (values : List α) :
    Encoding.encodeList id (values.map encode) = Encoding.encodeList encode values := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

/-- A measured execution of the actual finite record iterator, including
initial reset/pop and both parser and branch instructions per record. -/
theorem fold_iterate_eval {α : Type*} (ports : RecordPrograms.Ports 25 288) (callback : Code)
    (encode : α → Word) (stepStore : α → Store → Store) (cost : α → Store → ℕ)
    (values : List α) (initial : Store)
    (hc : FoldCalls ports callback encode stepStore cost initial values)
    (regs : Fin 25 → Bool) (suffix : Word) (v pr f : Bool) :
    ∃ n ≤ 3 + foldBudget encode stepStore cost initial values, ∃ finalRegs,
      Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports ⟨regs, initial⟩ v pr f
          (Encoding.encodeList encode values ++ suffix) [])
        (RecordPrograms.state ports ⟨finalRegs, foldStore stepStore initial values⟩
          false true false suffix []) := by
  obtain ⟨n, hn, finalRegs, hr⟩ := fold_loop_eval ports callback encode stepStore cost
    values initial hc regs suffix
  have h1 := RecordPrograms.set_found_eval ports ⟨regs, initial⟩ v pr f false
    (Encoding.encodeList id (values.map encode) ++ suffix) []
  have h2 := RecordPrograms.pop_list_eval ports ⟨regs, initial⟩ (values.map encode) suffix v pr
  refine ⟨1 + (1 + n), by omega, finalRegs, ?_⟩
  simpa only [encodeList_map_id] using h1.seq (h2.seq hr)

end SubexponentialSAT.SubexpDenseRowTableProgram


/-! Actual encounter-order scope iteration. Each parsed numeric vertex
invokes the complete coordinate producer; record output and cleanup remain
instructions in the same finite program. -/

namespace SubexponentialSAT.SubexpDenseRowTableProgram

open BitProgram StructuredCalls

def scopeWord (render : ℕ → ℕ → Word) (D v : ℕ) : Word :=
  Encoding.encodeList id (coordinateWords (render v) D)

def scopeStep (render : ℕ → ℕ → Word) (D v : ℕ) (initial : Store) : Store :=
  Function.update initial 268 (true :: (Encoding.frame (scopeWord render D v) ++ initial 268))

def scopeCost (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ) (D v : ℕ) (_ : Store) : ℕ :=
  incidenceCost (render v) (cost v) D v

def scopeFrame (initial current : Store) : Prop :=
  ∀ i : Fin 288, i ≠ 268 → current i = initial i

theorem scopeFrame_refl (initial : Store) : scopeFrame initial initial := by
  intro i hi
  rfl

theorem scopeFrame_step (initial current : Store) (h : scopeFrame initial current)
    (render : ℕ → ℕ → Word) (D v : ℕ) :
    scopeFrame initial (scopeStep render D v current) := by
  intro i hi
  simpa [scopeStep, hi] using h i hi

theorem coordinateReady_scopeFrame (initial current : Store)
    (h : scopeFrame initial current) (D : ℕ)
    (ha : CoordinateReady ⟨fun _ => false, initial⟩ D) (regs : Fin 25 → Bool) :
    CoordinateReady ⟨regs, current⟩ D := by
  constructor
  · exact (h 264 (by decide)).trans ha.1
  · intro i hi
    have hn : i ≠ 268 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (h i hn).trans (ha.2 i hi)

theorem coordinateReady_scopeState (base : Data) (D : ℕ)
    (ha : CoordinateReady base D) (tail payload : Word) (v pr f : Bool) :
    CoordinateReady (RecordPrograms.state scopePorts base v pr f tail payload) D := by
  constructor
  · simpa [RecordPrograms.state, scopePorts] using ha.1
  · intro i hi
    have he := ha.2 i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [RecordPrograms.state, scopePorts] using he

theorem scope_call_eval (row : Code) (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ)
    (D v : ℕ) (initial : Store) (regs : Fin 25 → Bool) (tail : Word)
    (ha : CoordinateReady ⟨regs, initial⟩ D)
    (hrow : RowContract row (render v) (cost v)
      (vertexReady (RecordPrograms.state scopePorts ⟨regs, initial⟩ false true false
        tail (Encoding.encodeNat v).reverse) v) D) :
    ∃ n ≤ scopeCost render cost D v initial, ∃ finalRegs,
      Eval (incidenceCallback row) n
        (RecordPrograms.state scopePorts ⟨regs, initial⟩ false true false
          tail (Encoding.encodeNat v).reverse)
        (RecordPrograms.state scopePorts ⟨finalRegs, scopeStep render D v initial⟩
          false true false tail []) := by
  let a := RecordPrograms.state scopePorts ⟨regs, initial⟩ false true false
    tail (Encoding.encodeNat v).reverse
  have ha' : CoordinateReady a D := coordinateReady_scopeState _ _ ha _ _ _ _ _
  have hv : a.stacks 260 = (Encoding.encodeNat v).reverse := by
    simp [a, RecordPrograms.state, scopePorts]
  obtain ⟨n, hn, finalRegs, h19, h20, h21, hr⟩ :=
    incidenceCallback_eval row (render v) (cost v) a D v ha' hv hrow
  have he : incidenceResult a finalRegs (render v) D =
      RecordPrograms.state scopePorts ⟨finalRegs, scopeStep render D v initial⟩
        false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases h : i = 19
      · subst i; simpa [RecordPrograms.state, scopePorts] using h19
      by_cases h : i = 20
      · subst i; simpa [RecordPrograms.state, scopePorts] using h20
      by_cases h : i = 21
      · subst i; simpa [RecordPrograms.state, scopePorts] using h21
      simp_all [RecordPrograms.state, scopePorts]
    · funext i
      by_cases h : i = 259
      · subst i; simp [a, RecordPrograms.state, scopePorts, scopeStep]
      by_cases h : i = 260
      · subst i; simp [scopePorts]
      by_cases h : i = 268
      · subst i; simp [a, RecordPrograms.state, scopePorts, scopeStep, scopeWord]
      simp_all [incidenceResult, a, RecordPrograms.state, scopePorts, scopeStep]
  exact ⟨n, hn, finalRegs, by simpa only [he] using hr⟩

/-- Required row executions are indexed by the actual parsed vertex and the
current live state. The only varying stored word between scope callbacks is
the output accumulator; numeric indices are decoded by the running program. -/
def ScopeRows (row : Code) (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ)
    (D : ℕ) (initial : Store) (vertices : List ℕ) : Prop :=
  ∀ v ∈ vertices, ∀ current, scopeFrame initial current →
    ∀ (regs : Fin 25 → Bool) (tail : Word),
      RowContract row (render v) (cost v)
        (vertexReady (RecordPrograms.state scopePorts ⟨regs, current⟩ false true false
          tail (Encoding.encodeNat v).reverse) v) D

theorem scope_fold_calls (row : Code) (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ)
    (D : ℕ) (reference initial : Store) (vertices : List ℕ)
    (hframe : scopeFrame reference initial)
    (ha : CoordinateReady ⟨fun _ => false, reference⟩ D)
    (hrow : ScopeRows row render cost D reference vertices) :
    FoldCalls scopePorts (incidenceCallback row) Encoding.encodeNat
      (scopeStep render D) (scopeCost render cost D) initial vertices := by
  induction vertices generalizing initial with
  | nil => trivial
  | cons v vs ih =>
      constructor
      · intro regs tail
        exact scope_call_eval row render cost D v initial regs tail
          (coordinateReady_scopeFrame reference initial hframe D ha regs)
          (hrow v (by simp) initial hframe regs tail)
      · apply ih (scopeStep render D v initial)
          (scopeFrame_step reference initial hframe render D v)
        intro w hw current hcurrent regs tail
        exact hrow w (by simp [hw]) current hcurrent regs tail

/-- Full scope iteration in its actual encounter order. Every incidence
builds its D coordinate rows, and the same fixed parser visits the next one. -/
theorem scope_iterate_eval (row : Code) (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ)
    (D : ℕ) (initial : Store) (vertices : List ℕ)
    (ha : CoordinateReady ⟨fun _ => false, initial⟩ D)
    (hrow : ScopeRows row render cost D initial vertices)
    (regs : Fin 25 → Bool) (v pr f : Bool) :
    ∃ n ≤ 3 + foldBudget Encoding.encodeNat (scopeStep render D)
      (scopeCost render cost D) initial vertices, ∃ finalRegs,
      Eval (RecordPrograms.iterate scopePorts (incidenceCallback row)) n
        (RecordPrograms.state scopePorts ⟨regs, initial⟩ v pr f (scopeCode vertices) [])
        (RecordPrograms.state scopePorts
          ⟨finalRegs, foldStore (scopeStep render D) initial vertices⟩ false true false [] []) := by
  have hc := scope_fold_calls row render cost D initial initial vertices
    (scopeFrame_refl _) ha hrow
  simpa only [scopeCode, List.append_nil] using
    fold_iterate_eval scopePorts (incidenceCallback row) Encoding.encodeNat
      (scopeStep render D) (scopeCost render cost D) vertices initial hc regs [] v pr f

def prependRecords : List Word → Word → Word
  | [], acc => acc
  | bits :: rest, acc => prependRecords rest (true :: (Encoding.frame bits ++ acc))

theorem scope_fold_store (render : ℕ → ℕ → Word) (D : ℕ) (vertices : List ℕ)
    (initial : Store) :
    foldStore (scopeStep render D) initial vertices =
      Function.update initial 268
        (prependRecords (vertices.map (scopeWord render D)) (initial 268)) := by
  induction vertices generalizing initial with
  | nil => simp [foldStore, prependRecords]
  | cons v vs ih =>
      rw [foldStore, ih]
      funext i
      by_cases hi : i = 268 <;> simp [scopeStep, prependRecords, Function.update_apply, hi]

theorem prependRecords_encode (records acc : List Word) :
    prependRecords records (Encoding.encodeList id acc) =
      Encoding.encodeList id (records.reverse ++ acc) := by
  induction records generalizing acc with
  | nil => simp [prependRecords]
  | cons bits rest ih =>
      change prependRecords rest (Encoding.encodeList id (bits :: acc)) = _
      simpa [List.reverse_cons, List.append_assoc] using ih (bits :: acc)

theorem scope_fold_accumulator (render : ℕ → ℕ → Word) (D : ℕ)
    (vertices : List ℕ) (initial : Store) (acc : List Word)
    (hacc : initial 268 = Encoding.encodeList id acc) :
    foldStore (scopeStep render D) initial vertices 268 =
      Encoding.encodeList id ((vertices.map (scopeWord render D)).reverse ++ acc) := by
  simp [scope_fold_store, hacc, prependRecords_encode]

theorem scope_fold_frame (render : ℕ → ℕ → Word) (D : ℕ)
    (vertices : List ℕ) (initial : Store) (i : Fin 288) (hi : i ≠ 268) :
    foldStore (scopeStep render D) initial vertices i = initial i := by
  simp [scope_fold_store, hi]

def scopeBudget (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ) (D : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => 6 * (Encoding.encodeNat v).length + incidenceCost (render v) (cost v) D v + 7 +
      scopeBudget render cost D vs

theorem foldBudget_scope_eq (render : ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ)
    (D : ℕ) (vertices : List ℕ) (initial : Store) :
    foldBudget Encoding.encodeNat (scopeStep render D) (scopeCost render cost D) initial vertices =
      scopeBudget render cost D vertices := by
  induction vertices generalizing initial with
  | nil => rfl
  | cons v vs ih => simp [foldBudget, scopeBudget, scopeCost, ih]

theorem prependRecords_append (left right : List Word) (acc : Word) :
    prependRecords (left ++ right) acc = prependRecords right (prependRecords left acc) := by
  induction left generalizing acc with
  | nil => rfl
  | cons bits rest ih => simpa [prependRecords] using ih (true :: (Encoding.frame bits ++ acc))

end SubexponentialSAT.SubexpDenseRowTableProgram


/-! The factor loop runs the checked scope traversal and increments the
literal unary factor counter once, including for empty scopes. -/

namespace SubexponentialSAT.SubexpDenseRowTableProgram

open BitProgram StructuredCalls

def factorReset (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 16 false) 17 true) 18 false,
    a.stacks⟩

theorem resetFactor_eval (a : Data) : Eval resetFactor 3 a (factorReset a) := by
  let b : Data := (StructuredProgram.Atom.set 16 false).eval a
  let c : Data := (StructuredProgram.Atom.set 17 true).eval b
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 16 false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (17 : Fin 25) true) b)
  have h3 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (18 : Fin 25) false) c)
  simpa [b, c, resetFactor, factorReset, atom, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h1.seq (h2.seq h3)

def factorInput (initial : Store) (regs : Fin 25 → Bool) (tail : Word) (vertices : List ℕ) : Data :=
  RecordPrograms.state factorPorts ⟨regs, initial⟩ false true false tail (scopeCode vertices).reverse

def factorScopeInput (initial : Store) (regs : Fin 25 → Bool) (tail : Word)
    (vertices : List ℕ) : Data := transferred 258 259 (factorInput initial regs tail vertices)

def factorStep (render : ℕ → ℕ → ℕ → Word) (D : ℕ) (vertices : List ℕ)
    (initial : Store) : Store :=
  Function.update (Function.update initial 261 (true :: initial 261)) 268
    (prependRecords (vertices.map (scopeWord (render (initial 261).length) D)) (initial 268))

def factorCost (render : ℕ → ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ → ℕ)
    (D : ℕ) (vertices : List ℕ) (initial : Store) : ℕ :=
  3 * (scopeCode vertices).length + 11 +
    scopeBudget (render (initial 261).length) (cost (initial 261).length) D vertices

def FactorReady (initial : Store) (D : ℕ) : Prop :=
  CoordinateReady ⟨fun _ => false, initial⟩ D ∧ initial 259 = [] ∧ initial 260 = []

theorem factorScopeInput_ready (initial : Store) (D : ℕ) (ha : FactorReady initial D)
    (regs : Fin 25 → Bool) (tail : Word) (vertices : List ℕ) :
    CoordinateReady (factorScopeInput initial regs tail vertices) D := by
  constructor
  · simpa [factorScopeInput, transferred, factorInput, RecordPrograms.state, factorPorts,
      StackRoutines.transferStacks] using ha.1.1
  · intro i hi
    have he := ha.1.2 i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [factorScopeInput, transferred, factorInput, RecordPrograms.state, factorPorts,
        StackRoutines.transferStacks] using he

/-- One actual factor callback, with all row executions supplied by the
single-row program on the concrete state after scope decoding. -/
theorem factor_call_eval (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (vertices : List ℕ) (initial : Store)
    (ha : FactorReady initial D) (regs : Fin 25 → Bool) (tail : Word)
    (hrow : ScopeRows row (render (initial 261).length) (cost (initial 261).length) D
      (factorScopeInput initial regs tail vertices).stacks vertices) :
    ∃ n ≤ factorCost render cost D vertices initial, ∃ finalRegs,
      Eval (factorCallback row) n (factorInput initial regs tail vertices)
        (RecordPrograms.state factorPorts ⟨finalRegs, factorStep render D vertices initial⟩
          false true false tail []) := by
  let a := factorInput initial regs tail vertices
  let b := factorScopeInput initial regs tail vertices
  have ht : Eval (transfer 258 259) (3 * (scopeCode vertices).length + 3) a b := by
    simpa [b, factorScopeInput, a, factorInput, RecordPrograms.state, factorPorts] using
      transfer_eval 258 259 (by decide) a
  have hb : CoordinateReady b D := factorScopeInput_ready initial D ha regs tail vertices
  have hsource : b.stacks 259 = scopeCode vertices := by
    simp [b, factorScopeInput, transferred, StackRoutines.transferStacks, factorInput,
      RecordPrograms.state, factorPorts, ha.2.1]
  have hpayload : b.stacks 260 = [] := by
    simp [b, factorScopeInput, transferred, StackRoutines.transferStacks, factorInput,
      RecordPrograms.state, factorPorts, ha.2.2]
  have hstart : RecordPrograms.state scopePorts b (b.regs 19) (b.regs 20) (b.regs 21)
      (scopeCode vertices) [] = b := by
    apply RecordPrograms.state_eq_self <;> first | rfl | exact hsource | exact hpayload
  obtain ⟨n, hn, scopeRegs, hs⟩ := scope_iterate_eval row (render (initial 261).length)
    (cost (initial 261).length) D b.stacks vertices hb hrow b.regs
    (b.regs 19) (b.regs 20) (b.regs 21)
  rw [hstart] at hs
  rw [foldBudget_scope_eq] at hn
  let c := RecordPrograms.state scopePorts
    ⟨scopeRegs, foldStore (scopeStep (render (initial 261).length) D) b.stacks vertices⟩
      false true false [] []
  let d := pushed 261 true c
  let e := factorReset d
  have hi : Eval (pushConstant 261 true) 2 c d := pushConstant_eval _ _ _
  have hr : Eval resetFactor 3 d e := resetFactor_eval d
  have he : e = RecordPrograms.state factorPorts
      ⟨e.regs, factorStep render D vertices initial⟩ false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases h16i : i = 16
      · subst i; simp [e, factorReset, factorPorts]
      by_cases h17i : i = 17
      · subst i; simp [e, factorReset, factorPorts]
      by_cases h18i : i = 18
      · subst i; simp [e, factorReset, factorPorts]
      simp [e, factorReset, factorPorts,
        h16i, h17i, h18i]
    · funext i
      by_cases h : i = 257
      · subst i; simp [d, c, b, pushed, RecordPrograms.state, scopePorts,
          factorPorts, factorStep, factorScopeInput, factorInput, transferred,
          StackRoutines.transferStacks, scope_fold_store]
      by_cases h : i = 258
      · subst i; simp [d, c, b, pushed, RecordPrograms.state, scopePorts,
          factorPorts, factorStep, factorScopeInput, factorInput, transferred,
          StackRoutines.transferStacks, scope_fold_store]
      by_cases h : i = 259
      · subst i; simp [d, c, pushed, RecordPrograms.state, scopePorts,
          factorPorts, factorStep, ha.2.1]
      by_cases h : i = 260
      · subst i; simp [d, c, pushed, RecordPrograms.state, scopePorts,
          factorPorts, factorStep, ha.2.2]
      by_cases h : i = 261
      · subst i; simp [d, c, b, pushed, RecordPrograms.state, scopePorts,
          factorPorts, factorStep, factorScopeInput, factorInput, transferred,
          StackRoutines.transferStacks, scope_fold_store]
      by_cases h : i = 268
      · subst i; simp [d, c, b, pushed, RecordPrograms.state, scopePorts,
          factorPorts, factorStep, factorScopeInput, factorInput, transferred,
          StackRoutines.transferStacks, scope_fold_store]
      simp_all [e, d, c, b, factorReset, pushed, RecordPrograms.state, scopePorts,
        factorPorts, factorStep, factorScopeInput, factorInput, transferred,
        StackRoutines.transferStacks, scope_fold_store]
  refine ⟨(3 * (scopeCode vertices).length + 3) + (n + (2 + 3)), ?_, e.regs, ?_⟩
  · dsimp [factorCost]
    omega
  · have run := ht.seq (hs.seq (hi.seq hr))
    change Eval (factorCallback row) _ a e at run
    rw [he] at run
    exact run

theorem factorReady_step (render : ℕ → ℕ → ℕ → Word) (D : ℕ)
    (vertices : List ℕ) (initial : Store) (ha : FactorReady initial D) :
    FactorReady (factorStep render D vertices initial) D := by
  constructor
  · constructor
    · simpa [factorStep] using ha.1.1
    · intro i hi
      have he := ha.1.2 i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [factorStep] using he
  · simpa [factorStep] using ha.2

/-- Positional collection of the required actual single-row executions.
It follows the parsed scope family and evolving physical factor counter. -/
def FactorRows (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (D : ℕ) : Store → List (List ℕ) → Prop
  | _, [] => True
  | initial, vertices :: rest =>
      (∀ (regs : Fin 25 → Bool) (tail : Word),
        ScopeRows row (render (initial 261).length) (cost (initial 261).length) D
          (factorScopeInput initial regs tail vertices).stacks vertices) ∧
      FactorRows row render cost D (factorStep render D vertices initial) rest

theorem factor_fold_calls (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (scopes : List (List ℕ)) (initial : Store)
    (ha : FactorReady initial D) (hrow : FactorRows row render cost D initial scopes) :
    FoldCalls factorPorts (factorCallback row) scopeCode
      (factorStep render D) (factorCost render cost D) initial scopes := by
  induction scopes generalizing initial with
  | nil => trivial
  | cons vertices rest ih =>
      constructor
      · intro regs tail
        exact factor_call_eval row render cost D vertices initial ha regs tail (hrow.1 regs tail)
      · exact ih (factorStep render D vertices initial) (factorReady_step render D vertices initial ha)
          hrow.2

theorem factor_fold_counter (render : ℕ → ℕ → ℕ → Word) (D : ℕ)
    (scopes : List (List ℕ)) (initial : Store) (e : ℕ) (he : initial 261 = unary e) :
    foldStore (factorStep render D) initial scopes 261 = unary (e + scopes.length) := by
  induction scopes generalizing initial e with
  | nil => simpa [foldStore] using he
  | cons vertices rest ih =>
      have hs : factorStep render D vertices initial 261 = unary (e + 1) := by
        simp [factorStep, he, unary, List.replicate_succ]
      have hr := ih (factorStep render D vertices initial) (e + 1) hs
      simpa [foldStore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

theorem factor_fold_accumulator (render : ℕ → ℕ → ℕ → Word) (D : ℕ)
    (scopes : List (List ℕ)) (initial : Store) (e : ℕ) (he : initial 261 = unary e) :
    foldStore (factorStep render D) initial scopes 268 =
      prependRecords (incidenceRows render D e scopes) (initial 268) := by
  induction scopes generalizing initial e with
  | nil => rfl
  | cons vertices rest ih =>
      have hs : factorStep render D vertices initial 261 = unary (e + 1) := by
        simp [factorStep, he, unary, List.replicate_succ]
      have hr := ih (factorStep render D vertices initial) (e + 1) hs
      have hscope : scopeWord (render e) D =
          fun v => Encoding.encodeList id (coordinateRows render D e v) := by
        funext v
        rfl
      simpa [foldStore, factorStep, he, unary, incidenceRows,
        prependRecords_append, hscope] using hr

theorem factor_fold_frame (render : ℕ → ℕ → ℕ → Word) (D : ℕ)
    (scopes : List (List ℕ)) (initial : Store) (i : Fin 288)
    (h261 : i ≠ 261) (h268 : i ≠ 268) :
    foldStore (factorStep render D) initial scopes i = initial i := by
  induction scopes generalizing initial with
  | nil => rfl
  | cons vertices rest ih => simp [foldStore, ih, factorStep, h261, h268]

theorem factor_fold_store (render : ℕ → ℕ → ℕ → Word) (D : ℕ)
    (scopes : List (List ℕ)) (initial : Store) (e : ℕ) (he : initial 261 = unary e) :
    foldStore (factorStep render D) initial scopes =
      Function.update (Function.update initial 261 (unary (e + scopes.length))) 268
        (prependRecords (incidenceRows render D e scopes) (initial 268)) := by
  funext i
  by_cases hi : i = 261
  · subst i; simpa using factor_fold_counter render D scopes initial e he
  by_cases hj : i = 268
  · subst i; simpa using factor_fold_accumulator render D scopes initial e he
  simpa [hi, hj] using factor_fold_frame render D scopes initial i hi hj

end SubexponentialSAT.SubexpDenseRowTableProgram


/-! Full execution boundary for the fixed factor/scope/coordinate table
traversal. The remaining row premise is an actual call trace at every live
state; it is deliberately not asserted by this traversal theorem. -/

namespace SubexponentialSAT.SubexpDenseRowTableProgram

open BitProgram StructuredCalls

def TableReady (a : Data) (D : ℕ) (scopes : List (List ℕ)) : Prop :=
  a.stacks 256 = scopesCode scopes ∧ a.stacks 264 = unary D ∧
    ∀ i ∈ ([87, 255, 257, 258, 259, 260, 261, 262, 263, 266, 267, 268, 269, 270] :
      List (Fin 288)), a.stacks i = []

def tablePrepared (a : Data) : Data := pushed 268 false (copied 256 257 a)

theorem tablePrepared_factorReady (a : Data) (D : ℕ) (scopes : List (List ℕ))
    (ha : TableReady a D scopes) : FactorReady (tablePrepared a).stacks D := by
  constructor
  · constructor
    · simpa [tablePrepared, pushed, copied, StackRoutines.copyStacks] using ha.2.1
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [tablePrepared, pushed, copied, StackRoutines.copyStacks] using
          ha.2.2 _ (by simp)
  · constructor <;> simpa [tablePrepared, pushed, copied, StackRoutines.copyStacks] using
      ha.2.2 _ (by simp)

def tableResult (a : Data) (regs : Fin 25 → Bool) (render : ℕ → ℕ → ℕ → Word)
    (D : ℕ) (scopes : List (List ℕ)) : Data :=
  ⟨regs, Function.update (Function.update (Function.update (Function.update a.stacks
    256 []) 264 []) 265 []) 255 (tableCode render D scopes)⟩

def tableRunCost (a : Data) (render : ℕ → ℕ → ℕ → Word) (cost : ℕ → ℕ → ℕ → ℕ)
    (D : ℕ) (scopes : List (List ℕ)) : ℕ :=
  foldBudget scopeCode (factorStep render D) (factorCost render cost D)
    (tablePrepared a).stacks scopes + 9 * (scopesCode scopes).length +
    2 * scopes.length + 2 * D + 2 * (a.stacks 265).length + 24 +
    10 * (Encoding.encodeList id (incidenceRows render D 0 scopes).reverse).length

/-- The actual nested traversal consumes its runtime scope/dimension/lookup
masters and returns the complete incidence-major table. It restores every
other stack, including all fixed source arithmetic and cache data. -/
theorem command_eval (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (a : Data) (D : ℕ) (scopes : List (List ℕ))
    (ha : TableReady a D scopes)
    (hrows : FactorRows row render cost D (tablePrepared a).stacks scopes) :
    ∃ n ≤ tableRunCost a render cost D scopes, ∃ regs,
      Eval (command row) n a (tableResult a regs render D scopes) := by
  have h256 := ha.1
  have h264 := ha.2.1
  have h255 : a.stacks 255 = [] := ha.2.2 _ (by simp)
  have h257 : a.stacks 257 = [] := ha.2.2 _ (by simp)
  have h258 : a.stacks 258 = [] := ha.2.2 _ (by simp)
  have h261 : a.stacks 261 = [] := ha.2.2 _ (by simp)
  have h268 : a.stacks 268 = [] := ha.2.2 _ (by simp)
  have h269 : a.stacks 269 = [] := ha.2.2 _ (by simp)
  have h270 : a.stacks 270 = [] := ha.2.2 _ (by simp)
  let b := copied 256 257 a
  let c := tablePrepared a
  have hc : Eval (copy 256 257) (7 * (scopesCode scopes).length + 5) a b := by
    simpa [h256] using copy_eval 256 257 (by decide) (by decide) (by decide) a h270
  have hp : Eval (pushConstant 268 false) 2 b c := pushConstant_eval _ _ _
  have hsource : c.stacks 257 = scopesCode scopes := by
    simp [c, tablePrepared, pushed, copied, StackRoutines.copyStacks, h256, h257]
  have hpayload : c.stacks 258 = [] := by
    simp [c, tablePrepared, pushed, copied, StackRoutines.copyStacks, h258]
  have hcounter : c.stacks 261 = unary 0 := by
    simp [c, tablePrepared, pushed, copied, StackRoutines.copyStacks, h261, unary]
  have hacc : c.stacks 268 = Encoding.encodeList id ([] : List Word) := by
    simp [c, tablePrepared, pushed, copied, StackRoutines.copyStacks, h268, Encoding.encodeList]
  have hstart : RecordPrograms.state factorPorts c (c.regs 16) (c.regs 17) (c.regs 18)
      (scopesCode scopes) [] = c := by
    apply RecordPrograms.state_eq_self <;> first | rfl | exact hsource | exact hpayload
  have hcalls := factor_fold_calls row render cost D scopes c.stacks
    (tablePrepared_factorReady a D scopes ha) hrows
  obtain ⟨n, hn, rf, hs⟩ := fold_iterate_eval factorPorts (factorCallback row) scopeCode
    (factorStep render D) (factorCost render cost D) scopes c.stacks hcalls c.regs []
    (c.regs 16) (c.regs 17) (c.regs 18)
  simp only [List.append_nil] at hs
  change Eval (RecordPrograms.iterate factorPorts (factorCallback row)) n
    (RecordPrograms.state factorPorts c (c.regs 16) (c.regs 17) (c.regs 18)
      (scopesCode scopes) []) _ at hs
  rw [hstart] at hs
  let d := RecordPrograms.state factorPorts
    ⟨rf, foldStore (factorStep render D) c.stacks scopes⟩ false true false [] []
  have hdCounter : d.stacks 261 = unary scopes.length := by
    simp only [d, RecordPrograms.state, factorPorts]
    simpa using factor_fold_counter render D scopes c.stacks 0 hcounter
  have hfold := factor_fold_store render D scopes c.stacks 0 hcounter
  have hdFrame (i : Fin 288) (h257i : i ≠ 257) (h258i : i ≠ 258)
      (h261i : i ≠ 261) (h268i : i ≠ 268) : d.stacks i = a.stacks i := by
    calc
      d.stacks i = foldStore (factorStep render D) c.stacks scopes i := by
        simp [d, RecordPrograms.state, factorPorts, h257i, h258i]
      _ = c.stacks i := factor_fold_frame render D scopes c.stacks i h261i h268i
      _ = a.stacks i := by
        simp [c, tablePrepared, pushed, copied, StackRoutines.copyStacks, h257i, h268i]
  let e := cleared 261 d
  let f := cleared 256 e
  let g := cleared 264 f
  let h := cleared 265 g
  let j := pushed 255 false h
  have h1 : Eval (clear 261) (2 * scopes.length + 3) d e := by
    simpa [hdCounter, unary] using clear_eval 261 d
  have h2 : Eval (clear 256) (2 * (scopesCode scopes).length + 3) e f := by
    have he256 : e.stacks 256 = scopesCode scopes := by
      simpa [e, cleared, StackRoutines.clearStacks, h256] using
        hdFrame 256 (by decide) (by decide) (by decide) (by decide)
    simpa only [he256] using clear_eval 256 e
  have h3 : Eval (clear 264) (2 * D + 3) f g := by
    have hf264 : f.stacks 264 = unary D := by
      simpa [f, e, cleared, StackRoutines.clearStacks, h264] using
        hdFrame 264 (by decide) (by decide) (by decide) (by decide)
    simpa only [hf264, unary, List.length_replicate] using clear_eval 264 f
  have h4 : Eval (clear 265) (2 * (a.stacks 265).length + 3) g h := by
    have hg265 : g.stacks 265 = a.stacks 265 := by
      simpa [g, f, e, cleared, StackRoutines.clearStacks] using
        hdFrame 265 (by decide) (by decide) (by decide) (by decide)
    simpa only [hg265] using clear_eval 265 g
  have h5 : Eval (pushConstant 255 false) 2 h j := pushConstant_eval _ _ _
  let records := (incidenceRows render D 0 scopes).reverse
  have hjSource : j.stacks 268 = Encoding.encodeList id records ++ [] := by
    simp [j, h, g, f, e, d, pushed, cleared, StackRoutines.clearStacks,
      RecordPrograms.state, factorPorts, hfold, hacc, prependRecords_encode, records]
  have hjTarget : j.stacks 255 = Encoding.encodeList id ([] : List Word) := by
    have hd255 := hdFrame 255 (by decide) (by decide) (by decide) (by decide)
    simp [j, h, g, f, e, pushed, cleared, StackRoutines.clearStacks,
      hd255, h255, Encoding.encodeList]
  have hjWork : j.stacks 269 = [] := by
    have hd269 := hdFrame 269 (by decide) (by decide) (by decide) (by decide)
    simp [j, h, g, f, e, pushed, cleared, StackRoutines.clearStacks, hd269, h269]
  obtain ⟨m, hm, hr⟩ := reverseRecords_eval 268 255 (by decide) (by decide)
    (by decide) (by decide) (by decide) j records [] [] hjSource hjTarget hjWork
  let final := reversedRecords 268 255 records [] [] j
  have hfinal : final = tableResult a final.regs render D scopes := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h255i : i = 255
      · subst i; simp [tableCode, records]
      by_cases h256i : i = 256
      · subst i; simp [j, h, g, f, cleared, pushed,
          StackRoutines.clearStacks]
      by_cases h264i : i = 264
      · subst i; simp [j, h, g, cleared, pushed,
          StackRoutines.clearStacks]
      by_cases h265i : i = 265
      · subst i; simp [j, h, cleared, pushed,
          StackRoutines.clearStacks]
      by_cases h261i : i = 261
      · subst i; simp [j, h, g, f, e, cleared, pushed,
          StackRoutines.clearStacks, h261]
      by_cases h268i : i = 268
      · subst i; simp [h268]
      by_cases h257i : i = 257
      · subst i; simp [j, h, g, f, e, d, cleared, pushed,
          StackRoutines.clearStacks, RecordPrograms.state, factorPorts, h257]
      by_cases h258i : i = 258
      · subst i; simp [j, h, g, f, e, d, cleared, pushed,
          StackRoutines.clearStacks, RecordPrograms.state, factorPorts, h258]
      have hdi := hdFrame i h257i h258i h261i h268i
      simp [j, h, g, f, e, cleared, pushed,
        StackRoutines.clearStacks, hdi,
        h255i, h256i, h264i, h265i, h261i, h268i]
  have run := hc.seq (hp.seq (hs.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq hr)))))))
  refine ⟨(7 * (scopesCode scopes).length + 5) + (2 + (n +
    ((2 * scopes.length + 3) + ((2 * (scopesCode scopes).length + 3) +
      ((2 * D + 3) + ((2 * (a.stacks 265).length + 3) + (2 + m))))))),
    ?_, final.regs, ?_⟩
  · dsimp [tableRunCost]
    change m ≤ 10 * (Encoding.encodeList id (incidenceRows render D 0 scopes).reverse).length at hm
    change n ≤ 3 + foldBudget scopeCode (factorStep render D) (factorCost render cost D)
      (tablePrepared a).stacks scopes at hn
    omega
  · change Eval (command row) _ a final at run
    rw [hfinal] at run
    exact run

theorem program_runsIn (row : Code) (render : ℕ → ℕ → ℕ → Word)
    (cost : ℕ → ℕ → ℕ → ℕ) (a : Data) (D : ℕ) (scopes : List (List ℕ))
    (ha : TableReady a D scopes)
    (hrows : FactorRows row render cost D (tablePrepared a).stacks scopes) :
    ∃ regs, RunsIn (program row) (tableRunCost a render cost D scopes + 1)
      (a.withPC (some (program row).entry))
      ((tableResult a regs render D scopes).withPC none) := by
  obtain ⟨n, hn, regs, he⟩ := command_eval row render cost a D scopes ha hrows
  exact ⟨regs, n + 1, by omega, compiled_halt_trace he 256 255⟩

theorem tableResult_output (a : Data) (regs : Fin 25 → Bool)
    (render : ℕ → ℕ → ℕ → Word) (D : ℕ) (scopes : List (List ℕ)) :
    (tableResult a regs render D scopes).stacks 255 = tableCode render D scopes := by
  simp [tableResult]

theorem tableResult_frame (a : Data) (regs : Fin 25 → Bool)
    (render : ℕ → ℕ → ℕ → Word) (D : ℕ) (scopes : List (List ℕ))
    (i : Fin 288) (h255 : i ≠ 255) (h256 : i ≠ 256) (h264 : i ≠ 264) (h265 : i ≠ 265) :
    (tableResult a regs render D scopes).stacks i = a.stacks i := by
  simp [tableResult, h255, h256, h264, h265]

end SubexponentialSAT.SubexpDenseRowTableProgram

end OAI.Algorithms
