import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpChunkRecordMap

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

abbrev initializeOutput : Cmd 11 22 := .base (.atom (.push 20 0))
abbrev seedSource : Cmd 11 22 := .base (.atom (.push 19 0))

theorem initialize_eval (ell source : List Bool) :
    Eval initializeOutput 1 (data false false false ell source [] [])
      (data false false false ell source [false] []) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 11) (s := 22) 20 0)
    (data false false false ell source [] [])
  have he : (StructuredProgram.Atom.push (r := 11) (s := 22) 20 0).eval
      (data false false false ell source [] []) =
        data false false false ell source [false] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at h
  exact .base h

theorem seedSource_eval (ell output : List Bool) :
    Eval seedSource 1 (data false true false ell [] output [])
      (data false true false ell [false] output []) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 11) (s := 22) 19 0)
    (data false true false ell [] output [])
  have he : (StructuredProgram.Atom.push (r := 11) (s := 22) 19 0).eval
      (data false true false ell [] output []) =
        data false true false ell [false] output [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at h
  exact .base h

def reverseStacks : Fin 4 → Fin 22 := ![20, 21, 19, 9]
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverse : Cmd 11 22 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitRegisters reverseStacks)

private theorem embed_reverse (v pr found oldV oldPr oldFound : Bool)
    (ell source output payload oldSource oldOutput : List Bool) :
    embedState emitRegisters reverseStacks
      (data oldV oldPr oldFound ell oldSource oldOutput [])
      (SubexpNormalizeProgram.filterState v pr found output [] source payload) =
        data v pr found ell source output payload := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective reverseStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2, h.symm⟩
    simp only [data, regs, h8, h9, h10, ite_false]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ 9 := fun h => hi ⟨3, h.symm⟩
    have h19 : i ≠ 19 := fun h => hi ⟨2, h.symm⟩
    have h20 : i ≠ 20 := fun h => hi ⟨0, h.symm⟩
    simp only [data, tapes, h9, h19, h20, ite_false]

theorem reverse_eval (ell : List Bool) (codes : List ℕ) :
    ∃ t ≤ 10 * (Encoding.encodeList Encoding.encodeNat codes).length,
      Eval reverse t
        (data false true false ell [false]
          (Encoding.encodeList Encoding.encodeNat codes.reverse) [])
        (data false true false ell (Encoding.encodeList Encoding.encodeNat codes) [] []) := by
  obtain ⟨t, ht, he⟩ := SubexpNormalizeProgram.reverseRecords_runsIn
    (codes.reverse.map Encoding.encodeNat) [] [] [] false true false
  have h := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitRegisters reverseStacks
    (data false true false ell [false]
      (Encoding.encodeList Encoding.encodeNat codes.reverse) [])
    emitRegisters_injective reverseStacks_injective he
  have hreverse : (codes.reverse.map Encoding.encodeNat).reverse = codes.map Encoding.encodeNat := by
    simp only [List.map_reverse, List.reverse_reverse]
  simp only [List.append_nil, hreverse,
    ExecLiteralDedupProgram.encode_nat_records, Encoding.encodeList, embed_reverse] at h
  refine ⟨t, ?_, h⟩
  rw [List.map_reverse, ExecLiteralDedupProgram.encoded_reverse_length,
    ExecLiteralDedupProgram.encode_nat_records] at ht
  exact ht

def dedupRegisters : Fin 10 → Fin 11 := Fin.castAdd 1
def dedupStacks : Fin 8 → Fin 22 := ![19, 9, 20, 0, 1, 2, 3, 21]

theorem dedupRegisters_injective : Function.Injective dedupRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
theorem dedupStacks_injective : Function.Injective dedupStacks := by decide

abbrev dedup : Cmd 11 22 := .call (ProgramLinking.liftProgram
  ExecLiteralDedupProgram.dedupProgram dedupRegisters dedupStacks)

private theorem embed_restricted {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (d : State R S) :
    embedState register stack d ⟨d.regs ∘ register, d.stacks ∘ stack⟩ = d := by
  apply embedState_eq_of_ports _ _ _ _ _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

theorem dedup_eval (ell : List Bool) (codes : List ℕ) :
    ∃ t ≤ 120 * ((Encoding.encodeList Encoding.encodeNat codes).length + 1) ^ 2,
      ∃ rf, Eval dedup t
        (data false true false ell (Encoding.encodeList Encoding.encodeNat codes) [] [])
        (⟨rf, tapes ell
          (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] []⟩ : Data) := by
  let d := data false true false ell (Encoding.encodeList Encoding.encodeNat codes) [] []
  let localState : State 10 8 := ⟨d.regs ∘ dedupRegisters, d.stacks ∘ dedupStacks⟩
  have hready : ExecLiteralDedupProgram.Ready localState := by
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  obtain ⟨e, heReady, hout, t, ht, he⟩ := ExecLiteralDedupProgram.literal_runsIn
    codes localState rfl hready
  have h := eval_call_lifted ExecLiteralDedupProgram.dedupProgram dedupRegisters dedupStacks
    d dedupRegisters_injective dedupStacks_injective he
  change Eval dedup t (embedState _ _ d localState) (embedState _ _ d e) at h
  rw [embed_restricted _ _ dedupRegisters_injective dedupStacks_injective] at h
  let result := embedState dedupRegisters dedupStacks d e
  have hs : result.stacks = tapes ell
      (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] [] := by
    have hp (i : Fin 8) :
        (tapes ell (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] [])
          (dedupStacks i) = e.stacks i := by
      rcases heReady with ⟨⟨h3, h4, h5, h6, h7⟩, h1, h2⟩
      fin_cases i
      · exact hout.symm
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
      · exact h4.symm
      · exact h5.symm
      · exact h6.symm
      · exact h7.symm
    funext i
    by_cases hi : ∃ j, dedupStacks j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack _ _ _ _ dedupStacks_injective j).trans (hp j).symm
    · have h19 : i ≠ 19 := fun hh => hi ⟨0, hh.symm⟩
      rw [show result.stacks i = d.stacks i from
        embedState_stack_frame _ _ _ _ _ hi]
      simp only [d, data, tapes, h19, ite_false]
  have hr : result = (⟨result.regs, tapes ell
      (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] []⟩ : Data) :=
    state_ext rfl hs
  exact ⟨t, ht, result.regs, by simpa only [← hr] using h⟩

def scope (ell : List Bool) (codes : List ℕ) : List ℕ :=
  ExecCNF.dedupLiterals (codes.map (chunk ell))

@[simp] theorem mem_scope (ell : List Bool) (codes : List ℕ) (j : ℕ) :
    j ∈ scope ell codes ↔ ∃ code ∈ codes, (code / 2) / BinaryArithmetic.toNat ell = j := by
  simp only [scope, ExecCNF.mem_dedupLiterals, List.mem_map, chunk]

theorem scope_nodup (ell : List Bool) (codes : List ℕ) : (scope ell codes).Nodup :=
  ExecCNF.dedupLiterals_nodup _

theorem scope_length_le (ell : List Bool) (codes : List ℕ) :
    (scope ell codes).length ≤ codes.length := by
  exact (ExecCNF.dedupLiterals_length_le _).trans_eq (List.length_map ..)

theorem scope_lt {D n : ℕ} (ell : List Bool) (codes : List ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell)
    (hn : n ≤ D * BinaryArithmetic.toNat ell)
    (hcodes : ∀ code ∈ codes, code / 2 < n) :
    ∀ j ∈ scope ell codes, j < D := by
  intro j hj
  obtain ⟨code, hc, he⟩ := (mem_scope ell codes j).mp hj
  rw [← he]
  exact (Nat.div_lt_iff_lt_mul hell).mpr ((hcodes code hc).trans_le hn)

/-- Proof-carrying view of the same emitted numeric scope; its values and
order are unchanged. The machine does not execute the bound proof. -/
def typedScope {D : ℕ} (ell : List Bool) (codes : List ℕ)
    (hbound : ∀ j ∈ scope ell codes, j < D) : List (Fin D) :=
  (scope ell codes).attach.map (fun j => ⟨j.val, hbound j.val j.property⟩)

@[simp] theorem typedScope_values {D : ℕ} (ell : List Bool) (codes : List ℕ)
    (hbound : ∀ j ∈ scope ell codes, j < D) :
    (typedScope ell codes hbound).map Fin.val = scope ell codes := by
  simp only [typedScope, List.map_map, Function.comp_def]
  exact List.attach_map_subtype_val _

@[simp] theorem typedScope_length {D : ℕ} (ell : List Bool) (codes : List ℕ)
    (hbound : ∀ j ∈ scope ell codes, j < D) :
    (typedScope ell codes hbound).length = (scope ell codes).length := by
  have h := congrArg List.length (typedScope_values ell codes hbound)
  simpa only [List.length_map] using h

theorem typedScope_nodup {D : ℕ} (ell : List Bool) (codes : List ℕ)
    (hbound : ∀ j ∈ scope ell codes, j < D) :
    (typedScope ell codes hbound).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [typedScope_values]
  exact scope_nodup ell codes

@[simp] theorem mem_typedScope {D : ℕ} (ell : List Bool) (codes : List ℕ)
    (hbound : ∀ j ∈ scope ell codes, j < D) (j : Fin D) :
    j ∈ typedScope ell codes hbound ↔ j.val ∈ scope ell codes := by
  rw [← typedScope_values ell codes hbound]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨j, h, rfl⟩
  · intro h
    obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    have hij : i = j := Fin.ext he
    simpa only [hij] using hi

abbrev command : Cmd 11 22 := .seq initializeOutput (.seq scan
  (.seq seedSource (.seq reverse dedup)))

/-- Every term counts instructions in a concrete pass over an actual encoding. -/
def budget (ell : List Bool) (codes : List ℕ) : ℕ :=
  5 + RecordPrograms.budget (callbackCost ell) (codes.map Encoding.encodeNat) +
    10 * (Encoding.encodeList Encoding.encodeNat (codes.map (chunk ell))).length +
    120 * ((Encoding.encodeList Encoding.encodeNat (codes.map (chunk ell))).length + 1) ^ 2

theorem command_eval (ell : List Bool) (codes : List ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ budget ell codes, ∃ rf,
      Eval command t (data false false false ell (Encoding.encodeList Encoding.encodeNat codes) [] [])
        (⟨rf, tapes ell (Encoding.encodeList Encoding.encodeNat (scope ell codes)) [] []⟩ : Data) := by
  have hi := initialize_eval ell (Encoding.encodeList Encoding.encodeNat codes)
  obtain ⟨ns, hns, hs⟩ := scan_eval ell codes [] [] hell false false false
  simp only [List.append_nil, Encoding.encodeList] at hs
  have hp := seedSource_eval ell (Encoding.encodeList Encoding.encodeNat (codes.map (chunk ell)).reverse)
  obtain ⟨nr, hnr, hr⟩ := reverse_eval ell (codes.map (chunk ell))
  obtain ⟨nd, hnd, rf, hd⟩ := dedup_eval ell (codes.map (chunk ell))
  refine ⟨1 + (ns + (1 + (nr + nd))), ?_, rf, hi.seq (hs.seq (hp.seq (hr.seq hd)))⟩
  unfold budget
  omega

def program := compiled command (19 : Fin 22) 19

theorem program_runsIn (ell : List Bool) (codes : List ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ rf, RunsIn program (budget ell codes + 1)
      ((data false false false ell (Encoding.encodeList Encoding.encodeNat codes) [] []).withPC
        (some program.entry))
      ((⟨rf, tapes ell (Encoding.encodeList Encoding.encodeNat (scope ell codes)) [] []⟩ : Data).withPC none) := by
  obtain ⟨t, ht, rf, he⟩ := command_eval ell codes hell
  exact ⟨rf, t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 19 19⟩

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
