import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionCallback

namespace OAI.Algorithms

/-! Scan the ordered type buckets for one complete block. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Entry := List Bool × List (List Bool)

def entryWord (e : Entry) : List Bool := bucketWord e.1 e.2
def entryVertex (i : ℕ) (e : Entry) : List Bool := e.2.getD i []

def base (regs : Fin 8 → Bool) (c : Context) : Data :=
  ready regs { c with keys := [], payload := [] }

def parserRegs (regs : Fin 8 → Bool) (tag present found : Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 tag) 6 present) 7 found

theorem parser_state (regs : Fin 8 → Bool) (c : Context)
    (tag present found : Bool) (keys payload : List Bool) :
    RecordPrograms.state ports (ready regs c) tag present found keys payload =
    ready (parserRegs regs tag present found) { c with keys := keys, payload := payload } := by
  apply MatrixProgramSupport.data_ext <;> try rfl
  funext j
  fin_cases j <;> simp [ready, state, RecordPrograms.state, ports]

theorem parserRegs_self (regs : Fin 8 → Bool) :
    parserRegs regs (regs 5) (regs 6) (regs 7) = regs := by
  funext j
  fin_cases j <;> simp [parserRegs]

theorem parserRegs_finish (regs : Fin 8 → Bool) :
    parserRegs (finishRegs regs) false true false = finishRegs regs := by
  funext j
  fin_cases j <;> simp [parserRegs, finishRegs]

theorem entry_split (i : ℕ) (e : Entry) (hi : i < e.2.length) :
    e.2.take i ++ entryVertex i e :: e.2.drop (i + 1) = e.2 := by
  rw [entryVertex, List.getD_eq_getElem e.2 [] hi, ← List.drop_eq_getElem_cons hi,
    List.take_append_drop]

theorem callback_entry_eval (i : ℕ) (e : Entry) (hi : i < e.2.length)
    (c : Context) (hblock : c.block = List.replicate i true) (regs : Fin 8 → Bool) :
    ∃ n ≤ callbackBudget (entryWord e) c.block c.address, ∃ rf,
      Eval callback n (ready regs { c with payload := (entryWord e).reverse })
        (ready (finishRegs rf) (emitted { c with payload := [] } e.1 (entryVertex i e))) := by
  have htake : (e.2.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hblock' : c.block = List.replicate (e.2.take i).length true := by
    simpa only [htake] using hblock
  simpa only [entry_split i e hi, entryWord] using
    callback_eval e.1 (entryVertex i e) (e.2.take i) (e.2.drop (i + 1)) c hblock' regs

def emitEntries (i : ℕ) (entries : List Entry) (c : Context) : Context :=
  entries.foldl (fun d e => emitted d e.1 (entryVertex i e)) c

def blockBudget (i : ℕ) : List Entry → Context → ℕ
  | [], _ => 0
  | e :: es, c => 6 * (entryWord e).length + callbackBudget (entryWord e) c.block c.address + 7 +
      blockBudget i es (emitted c e.1 (entryVertex i e))

theorem emitted_block (c : Context) (key vertex : List Bool) :
    (emitted c key vertex).block = c.block := rfl

theorem block_loop_eval (i : ℕ) (entries : List Entry) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hentries : ∀ e ∈ entries, i < e.2.length)
    (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ n ≤ 1 + blockBudget i entries c, ∃ rf,
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (base regs c) (entries.map entryWord) suffix)
        (RecordPrograms.state ports (base rf (emitEntries i entries c)) false true false suffix []) := by
  induction entries generalizing c regs with
  | nil =>
    refine ⟨1, by simp [blockBudget], regs, ?_⟩
    simpa only [List.map_nil, emitEntries, List.foldl_nil, RecordPrograms.afterTag] using
      (Eval.while_false (body := RecordPrograms.body ports callback)
        (a := RecordPrograms.state ports (base regs c) false true false suffix []) (by simp))
  | cons e es ih =>
    let a := base regs c
    let tail := Encoding.encodeList id (es.map entryWord) ++ suffix
    have hr : Eval (RecordPrograms.reader ports) (6 * (entryWord e).length + 4)
        (RecordPrograms.afterTag ports a ((e :: es).map entryWord) suffix)
        (RecordPrograms.state ports a false true false tail (entryWord e).reverse) := by
      simpa only [List.map_cons, RecordPrograms.afterTag, List.append_nil] using
        RecordPrograms.reader_eval ports a (entryWord e) tail [] true true false
    obtain ⟨nc, hnc, rc, hc⟩ := callback_entry_eval i e (hentries e (by simp))
      { c with keys := tail, payload := [] } hblock (parserRegs regs false true false)
    let d := emitted c e.1 (entryVertex i e)
    let b := base (finishRegs rc) d
    have hcb : Eval callback nc
        (RecordPrograms.state ports a false true false tail (entryWord e).reverse)
        (RecordPrograms.state ports b false true false tail []) := by
      simpa only [a, b, base, parser_state, parserRegs_finish, d, emitted] using hc
    have hbranch : Eval
        (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
          (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
        (RecordPrograms.state ports b false true false tail [])
        (RecordPrograms.afterTag ports b (es.map entryWord) suffix) := by
      apply Eval.ite_false (by simp)
      exact RecordPrograms.pop_list_eval ports b (es.map entryWord) suffix false true
    obtain ⟨nr, hnr, rf, hrest⟩ := ih d hblock
      (fun x hx => hentries x (by simp [hx])) (finishRegs rc)
    have hrun := Eval.while_true
      (show (RecordPrograms.afterTag ports a ((e :: es).map entryWord) suffix).regs ports.tag = true
        by simp [RecordPrograms.afterTag]) (hr.seq (hcb.seq hbranch)) hrest
    refine ⟨(6 * (entryWord e).length + 4 + (nc + 2)) + nr + 1, ?_, rf, ?_⟩
    · dsimp only at hnc
      dsimp only [d] at hnr
      simp only [blockBudget]
      omega
    · simpa only [RecordPrograms.loop, RecordPrograms.body, a, b, d, emitEntries,
        List.foldl_cons] using hrun

abbrev blockCommand : Cmd 8 19 := RecordPrograms.iterate ports callback

/-- A complete ordered bucket pass emits one actual vertex from every type. -/
theorem blockCommand_eval (i : ℕ) (entries : List Entry) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hentries : ∀ e ∈ entries, i < e.2.length) (regs : Fin 8 → Bool) (suffix : List Bool) :
    ∃ n ≤ 3 + blockBudget i entries c, ∃ rf, Eval blockCommand n
      (ready regs { c with
        keys := ProgramEncoding.encodeRecords (entries.map entryWord) ++ suffix
        payload := [] })
      (ready rf { (emitEntries i entries c) with keys := suffix, payload := [] }) := by
  let a := base regs c
  obtain ⟨n, hn, rf, he⟩ := block_loop_eval i entries c hblock hentries regs suffix
  have hset := RecordPrograms.set_found_eval ports a (regs 5) (regs 6) (regs 7) false
    (ProgramEncoding.encodeRecords (entries.map entryWord) ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports a (entries.map entryWord) suffix (regs 5) (regs 6)
  have hrun := hset.seq (hpop.seq he)
  refine ⟨1 + (1 + n), by omega, parserRegs rf false true false, ?_⟩
  simpa only [blockCommand, RecordPrograms.iterate, a, base, parser_state,
    parserRegs_self] using hrun

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
