import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseFamilyCallback
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms

namespace OAI.Algorithms

/-! The actual paired clause-family mapper, including physical concatenation
onto forward unary-prefix table and scope streams. -/

namespace SubexponentialSAT.SubexpClauseFamilyProgram

open BitProgram StructuredCalls SubexpClauseFamilySupport SubexpClauseFamilyCallback

abbrev Inputs := SubexpClauseFamilyCallback.Inputs
abbrev Valid := SubexpClauseFamilyCallback.Valid
abbrev Ready := SubexpClauseFamilyCallback.Ready
abbrev table := @SubexpClauseFamilyCallback.table
abbrev scopeBytes := @SubexpClauseFamilyCallback.scopeBytes

def ports : RecordPrograms.Ports 14 35 where
  tag := 11
  present := 12
  found := 13
  source := 31
  payload := 34
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

@[simp] theorem ready_state (c : Inputs) (base : Data)
    (v pr f : Bool) (src payload : List Bool) :
    Ready c (RecordPrograms.state ports base v pr f src payload) ↔ Ready c base := by
  simp [Ready, SubexpClauseFamilyCallback.Ready, RecordPrograms.state, ports]

@[simp] theorem state_table (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 32 = base.stacks 32 := by
  simp [RecordPrograms.state, ports]

@[simp] theorem state_scope (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 33 = base.stacks 33 := by
  simp [RecordPrograms.state, ports]

def tables {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) : List (List Bool) :=
  clauses.map (table c hv)

def scopes {n : ℕ} (c : Inputs)
    (clauses : List (List (SAT.Literal (Fin n)))) : List (List Bool) :=
  clauses.map (scopeBytes c)

def scanCost {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) : ℕ :=
  3 + RecordMappedPrograms.budget SubexpClauseRowProgram.clauseBytes (callbackCost c hv) clauses

/-- A numerical cap on the already-defined concrete callback cost gives a
linear input-record overhead; this does not posit any execution behavior. -/
theorem scanCost_le {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (K : ℕ)
    (hK : ∀ ls ∈ clauses, callbackCost c hv ls ≤ K) :
    scanCost c hv clauses ≤ (K + 17) *
      ((Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses).length + 1) := by
  have h := RecordMappedPrograms.program_budget_le_input
    SubexpClauseRowProgram.clauseBytes (callbackCost c hv) clauses 0 K (by
      intro ls hls
      simpa using hK ls hls)
  simp only [Nat.zero_add] at h
  unfold scanCost
  omega

theorem loop_eval {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (accTables accScopes : List (List Bool))
    (base : Data) (hready : Ready c base)
    (htables : base.stacks 32 = Encoding.encodeList id accTables)
    (hscopes : base.stacks 33 = Encoding.encodeList id accScopes) :
    ∃ t ≤ 1 + RecordMappedPrograms.budget SubexpClauseRowProgram.clauseBytes
        (callbackCost c hv) clauses, ∃ next : Data,
      Ready c next ∧
      next.stacks 32 = Encoding.encodeList id ((tables c hv clauses).reverse ++ accTables) ∧
      next.stacks 33 = Encoding.encodeList id ((scopes c clauses).reverse ++ accScopes) ∧
      Eval (RecordPrograms.loop ports callback) t
        (RecordMappedPrograms.afterTag ports SubexpClauseRowProgram.clauseBytes base clauses [])
        (RecordPrograms.state ports next false true false [] []) := by
  induction clauses generalizing base accTables accScopes with
  | nil =>
      refine ⟨1, by simp [RecordMappedPrograms.budget], base, hready, ?_, ?_, ?_⟩
      · simpa [tables] using htables
      · simpa [scopes] using hscopes
      · apply Eval.while_false
        simp [RecordMappedPrograms.afterTag]
  | cons ls rest ih =>
      let tail := Encoding.encodeList SubexpClauseRowProgram.clauseBytes rest
      let d := RecordPrograms.state ports base false true false tail
        (SubexpClauseRowProgram.clauseBytes ls).reverse
      have hd : Ready c d := (ready_state _ _ _ _ _ _ _).mpr hready
      obtain ⟨k, hk, middle, he, hm, hstacks, h11, h12, h13⟩ :=
        callback_eval c hv ls d hd (by simp [d, RecordPrograms.state, ports])
      have hm31 : middle.stacks 31 = tail := by
        simp [hstacks, d, RecordPrograms.state, ports]
      have hm34 : middle.stacks 34 = [] := by simp [hstacks]
      have hend : RecordPrograms.state ports middle false true false tail [] = middle :=
        RecordPrograms.state_eq_self ports middle false true false tail []
          h11 h12 h13 hm31 hm34
      have hcallback : Eval callback k d
          (RecordPrograms.state ports middle false true false tail []) := by
        rw [hend]; exact he
      have hmt : middle.stacks 32 = Encoding.encodeList id (table c hv ls :: accTables) := by
        simp [hstacks, d, htables, Encoding.encodeList]
      have hms : middle.stacks 33 = Encoding.encodeList id (scopeBytes c ls :: accScopes) := by
        simp [hstacks, d, hscopes, Encoding.encodeList]
      have hreader : Eval (RecordPrograms.reader ports)
          (6 * (SubexpClauseRowProgram.clauseBytes ls).length + 4)
          (RecordMappedPrograms.afterTag ports SubexpClauseRowProgram.clauseBytes
            base (ls :: rest) []) d := by
        simpa [RecordMappedPrograms.afterTag, tail, d] using
          RecordPrograms.reader_eval ports base (SubexpClauseRowProgram.clauseBytes ls)
            tail [] true true false
      have hbranch : Eval (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
          (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false tail [])
          (RecordMappedPrograms.afterTag ports SubexpClauseRowProgram.clauseBytes middle rest []) := by
        apply Eval.ite_false (by simp)
        simpa only [List.append_nil] using RecordMappedPrograms.pop_list_eval ports
          SubexpClauseRowProgram.clauseBytes middle rest [] false true
      obtain ⟨m, hmBound, next, hnReady, hnTables, hnScopes, hnEval⟩ :=
        ih (accTables := table c hv ls :: accTables)
          (accScopes := scopeBytes c ls :: accScopes) (base := middle) hm hmt hms
      have hguard : (RecordMappedPrograms.afterTag ports SubexpClauseRowProgram.clauseBytes
          base (ls :: rest) []).regs ports.tag = true := by
        simp [RecordMappedPrograms.afterTag]
      have hrun := Eval.while_true hguard (hreader.seq (hcallback.seq hbranch)) hnEval
      refine ⟨(6 * (SubexpClauseRowProgram.clauseBytes ls).length + 4 + (k + 2)) + m + 1,
        ?_, next, hnReady, ?_, ?_, ?_⟩
      · simp only [RecordMappedPrograms.budget]
        omega
      · simpa [tables, List.reverse_cons, List.append_assoc] using hnTables
      · simpa [scopes, List.reverse_cons, List.append_assoc] using hnScopes
      · simpa only [RecordPrograms.loop, RecordPrograms.body] using hrun

abbrev scan : Cmd 14 35 := RecordPrograms.iterate ports callback

theorem scan_eval {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (accTables accScopes : List (List Bool))
    (d : Data) (hready : Ready c d)
    (hsource : d.stacks 31 = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses)
    (hpayload : d.stacks 34 = [])
    (htables : d.stacks 32 = Encoding.encodeList id accTables)
    (hscopes : d.stacks 33 = Encoding.encodeList id accScopes) :
    ∃ t ≤ scanCost c hv clauses, ∃ e : Data,
      Eval scan t d e ∧ Ready c e ∧ e.stacks 31 = [] ∧ e.stacks 34 = [] ∧
      e.stacks 32 = Encoding.encodeList id ((tables c hv clauses).reverse ++ accTables) ∧
      e.stacks 33 = Encoding.encodeList id ((scopes c clauses).reverse ++ accScopes) := by
  obtain ⟨m, hm, next, hn, hnt, hns, hloop⟩ :=
    loop_eval c hv clauses accTables accScopes d hready htables hscopes
  have hstart : RecordPrograms.state ports d (d.regs 11) (d.regs 12) (d.regs 13)
      (Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses) [] = d :=
    RecordPrograms.state_eq_self ports d _ _ _ _ _ rfl rfl rfl hsource hpayload
  have hset := RecordPrograms.set_found_eval ports d (d.regs 11) (d.regs 12)
    (d.regs 13) false (Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses) []
  rw [hstart] at hset
  have hpop := RecordMappedPrograms.pop_list_eval ports SubexpClauseRowProgram.clauseBytes
    d clauses [] (d.regs 11) (d.regs 12)
  simp only [List.append_nil] at hpop
  let e := RecordPrograms.state ports next false true false [] []
  refine ⟨1 + (1 + m), by unfold scanCost; omega, e, hset.seq (hpop.seq hloop),
    (ready_state _ _ _ _ _ _ _).mpr hn, ?_, ?_, ?_, ?_⟩
  · simp [e, RecordPrograms.state, ports]
  · simp [e, RecordPrograms.state, ports]
  · simpa [e] using hnt
  · simpa [e] using hns

private theorem ready_update {c : Inputs} {d e : Data} (stream : Stream) (word : List Bool)
    (hd : Ready c d) (he : e.stacks = Function.update d.stacks stream.port word) : Ready c e := by
  intro i
  cases stream <;> simpa [he, Stream.port] using hd i

private theorem ready_25 {c : Inputs} {d : Data} (hd : Ready c d) : d.stacks 25 = [] := by
  simpa [Ready, SubexpClauseFamilyCallback.Ready, bankStack,
    SubexpClauseFactorProgram.tapes, withWord] using hd 25

abbrev command : Cmd 14 35 :=
  .seq (reverse .tables) (.seq (reverse .scopes)
    (.seq scan (.seq (reverse .tables) (reverse .scopes))))

/-- All four actual record reversals and the full parser/callback scan are
charged. In particular, pre-existing unary prefixes are not appended for free. -/
def budget {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (prefixTables prefixScopes : List (List Bool)) : ℕ :=
  (16 * (Encoding.encodeList id prefixTables).length + 8) +
  ((16 * (Encoding.encodeList id prefixScopes).length + 8) +
  (scanCost c hv clauses +
  ((16 * (Encoding.encodeList id ((tables c hv clauses).reverse ++ prefixTables.reverse)).length + 8) +
   (16 * (Encoding.encodeList id ((scopes c clauses).reverse ++ prefixScopes.reverse)).length + 8))))

theorem budget_eq {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (prefixTables prefixScopes : List (List Bool)) :
    budget c hv clauses prefixTables prefixScopes = scanCost c hv clauses +
      16 * ((Encoding.encodeList id prefixTables).length +
        (Encoding.encodeList id prefixScopes).length +
        (Encoding.encodeList id (prefixTables ++ tables c hv clauses)).length +
        (Encoding.encodeList id (prefixScopes ++ scopes c clauses)).length) + 32 := by
  have ht := ExecLiteralDedupProgram.encoded_reverse_length (prefixTables ++ tables c hv clauses)
  have hs := ExecLiteralDedupProgram.encoded_reverse_length (prefixScopes ++ scopes c clauses)
  simp only [List.reverse_append] at ht hs
  simp only [budget, ht, hs]
  ring

/-- Exact unary-first paired streams produced by one fixed finite command. -/
theorem command_eval {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (prefixTables prefixScopes : List (List Bool))
    (d : Data) (hready : Ready c d)
    (hsource : d.stacks 31 = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses)
    (hpayload : d.stacks 34 = [])
    (htables : d.stacks 32 = Encoding.encodeList id prefixTables)
    (hscopes : d.stacks 33 = Encoding.encodeList id prefixScopes) :
    ∃ t ≤ budget c hv clauses prefixTables prefixScopes, ∃ e : Data,
      Eval command t d e ∧ Ready c e ∧ e.stacks 31 = [] ∧ e.stacks 34 = [] ∧
      e.stacks 32 = Encoding.encodeList id (prefixTables ++ tables c hv clauses) ∧
      e.stacks 33 = Encoding.encodeList id (prefixScopes ++ scopes c clauses) := by
  obtain ⟨t₁, ht₁, a, he₁, ha⟩ :=
    reverse_eval .tables prefixTables d htables (ready_25 hready) hpayload
  have har : Ready c a := ready_update .tables _ hready ha
  have ha31 : a.stacks 31 = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses := by
    simpa [ha, Stream.port] using hsource
  have ha34 : a.stacks 34 = [] := by simpa [ha, Stream.port] using hpayload
  have ha32 : a.stacks 32 = Encoding.encodeList id prefixTables.reverse := by simp [ha, Stream.port]
  have ha33 : a.stacks 33 = Encoding.encodeList id prefixScopes := by simpa [ha, Stream.port] using hscopes
  obtain ⟨t₂, ht₂, b, he₂, hb⟩ :=
    reverse_eval .scopes prefixScopes a ha33 (ready_25 har) ha34
  have hbr : Ready c b := ready_update .scopes _ har hb
  have hb31 : b.stacks 31 = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses := by
    simpa [hb, Stream.port] using ha31
  have hb34 : b.stacks 34 = [] := by simpa [hb, Stream.port] using ha34
  have hb32 : b.stacks 32 = Encoding.encodeList id prefixTables.reverse := by
    simpa [hb, Stream.port] using ha32
  have hb33 : b.stacks 33 = Encoding.encodeList id prefixScopes.reverse := by simp [hb, Stream.port]
  obtain ⟨t₃, ht₃, middle, he₃, hm, hm31, hm34, hm32, hm33⟩ :=
    scan_eval c hv clauses prefixTables.reverse prefixScopes.reverse b hbr hb31 hb34 hb32 hb33
  obtain ⟨t₄, ht₄, f, he₄, hf⟩ := reverse_eval .tables
    ((tables c hv clauses).reverse ++ prefixTables.reverse) middle hm32 (ready_25 hm) hm34
  have hfr : Ready c f := ready_update .tables _ hm hf
  have hf31 : f.stacks 31 = [] := by simpa [hf, Stream.port] using hm31
  have hf34 : f.stacks 34 = [] := by simpa [hf, Stream.port] using hm34
  have hf32 : f.stacks 32 = Encoding.encodeList id (prefixTables ++ tables c hv clauses) := by
    simp [hf, Stream.port, List.reverse_append]
  have hf33 : f.stacks 33 = Encoding.encodeList id
      ((scopes c clauses).reverse ++ prefixScopes.reverse) := by
    simpa [hf, Stream.port] using hm33
  obtain ⟨t₅, ht₅, e, he₅, hfinal⟩ := reverse_eval .scopes
    ((scopes c clauses).reverse ++ prefixScopes.reverse) f hf33 (ready_25 hfr) hf34
  refine ⟨t₁ + (t₂ + (t₃ + (t₄ + t₅))), ?_, e,
    he₁.seq (he₂.seq (he₃.seq (he₄.seq he₅))), ready_update .scopes _ hfr hfinal, ?_, ?_, ?_, ?_⟩
  · unfold budget; omega
  · simpa [hfinal, Stream.port] using hf31
  · simpa [hfinal, Stream.port] using hf34
  · simpa [hfinal, Stream.port] using hf32
  · simp [hfinal, Stream.port, List.reverse_append]

def program := compiled command (31 : Fin 35) 32

theorem program_runsIn {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (prefixTables prefixScopes : List (List Bool))
    (d : Data) (hready : Ready c d)
    (hsource : d.stacks 31 = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses)
    (hpayload : d.stacks 34 = [])
    (htables : d.stacks 32 = Encoding.encodeList id prefixTables)
    (hscopes : d.stacks 33 = Encoding.encodeList id prefixScopes) :
    ∃ e : Data, Ready c e ∧ e.stacks 31 = [] ∧ e.stacks 34 = [] ∧
      e.stacks 32 = Encoding.encodeList id (prefixTables ++ tables c hv clauses) ∧
      e.stacks 33 = Encoding.encodeList id (prefixScopes ++ scopes c clauses) ∧
      RunsIn program (budget c hv clauses prefixTables prefixScopes + 1)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨t, ht, e, he, hr, hs, hp, htables, hscopes⟩ :=
    command_eval c hv clauses prefixTables prefixScopes d hready hsource hpayload htables hscopes
  exact ⟨e, hr, hs, hp, htables, hscopes, t + 1, Nat.add_le_add_right ht 1,
    compiled_halt_trace he 31 32⟩

theorem primitive_execution {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) (prefixTables prefixScopes : List (List Bool))
    (d : Data) (hready : Ready c d)
    (hsource : d.stacks 31 = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses)
    (hpayload : d.stacks 34 = [])
    (htables : d.stacks 32 = Encoding.encodeList id prefixTables)
    (hscopes : d.stacks 33 = Encoding.encodeList id prefixScopes) :
    ∃ e : Data, Ready c e ∧ e.stacks 31 = [] ∧ e.stacks 34 = [] ∧
      e.stacks 32 = Encoding.encodeList id (prefixTables ++ tables c hv clauses) ∧
      e.stacks 33 = Encoding.encodeList id (prefixScopes ++ scopes c clauses) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (budget c hv clauses prefixTables prefixScopes + 1))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, hr, hs, hp, htables, hscopes, he⟩ :=
    program_runsIn c hv clauses prefixTables prefixScopes d hready hsource hpayload htables hscopes
  exact ⟨e, hr, hs, hp, htables, hscopes, BitProgram.primitive_execution program he⟩

theorem paired_length {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (clauses : List (List (SAT.Literal (Fin n)))) :
    (tables c hv clauses).length = clauses.length ∧ (scopes c clauses).length = clauses.length := by
  simp [tables, scopes]

end SubexponentialSAT.SubexpClauseFamilyProgram

end OAI.Algorithms
