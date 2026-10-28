import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketExecution
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Closed global packet execution from the original physical input streams. -/

namespace SubexponentialSAT.SubexpFactorPacketProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word cacheBytes)

structure Inputs where
  origins : List (List Word)
  columns : List (List (List Word))
  scopes : List (List ℕ)
  tables : List Word
  cache : List (List Word)
  modulus : Word
  zero : Word
  one : Word

def groups (i : Inputs) := SubexpFactorPrefixProgram.grouped i.scopes i.origins i.columns
def factorInputs (i : Inputs) : List SubexpFactorPacketLocal.Input :=
  ((groups i).zip i.tables).map (fun pair => ⟨pair.1, pair.2⟩)

def masters (i : Inputs) : SubexpFactorPacketControl.Masters where
  cache := cacheBytes i.cache
  groups := SubexpFactorPrefixProgram.groupStream (groups i)
  tables := Encoding.encodeList id i.tables
  modulus := i.modulus
  zero := i.zero
  one := i.one

def initialMasters (i : Inputs) : SubexpFactorPacketControl.Masters :=
  {masters i with groups := []}

/-- These are projections of the input tapes. Neither field describes an
output, a polynomial value, or an execution of a callback. -/
structure Ready (d : Data) (i : Inputs) : Prop where
  prefix_eq : projectState registers prefixPorts d =
    SubexpFactorPrefixProgram.inputState (d.regs ∘ registers) i.origins i.columns i.scopes
  packet_eq : projectState registers packetPorts d =
    SubexpFactorPacketControl.state (d.regs ∘ registers) (initialMasters i)

def output (i : Inputs) : Word :=
  SubexpFactorPacketExecution.packetStream (masters i) i.cache (factorInputs i)

private theorem encode_map {A B : Type*} (enc : B → Word) (f : A → B) (xs : List A) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

def producedFactors (i : Inputs) : List (List Subexp.FactorBlueprint.Row) :=
  (factorInputs i).map (SubexpFactorPacketLocal.factorRows (masters i) i.cache)

theorem output_eq_encodeFactors (i : Inputs) :
    output i = Encoding.encodeList Subexp.FactorBlueprint.encodeRows (producedFactors i) := by
  symm
  exact encode_map Subexp.FactorBlueprint.encodeRows
    (SubexpFactorPacketLocal.factorRows (masters i) i.cache) (factorInputs i)

theorem factorInputs_projections (i : Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (htables : i.tables.length = i.scopes.length) :
    (factorInputs i).map SubexpFactorPacketLocal.Input.prefixes = groups i ∧
    (factorInputs i).map SubexpFactorPacketLocal.Input.answers = i.tables := by
  have hl : (groups i).length = i.tables.length := by
    have h := congrArg List.length
      (SubexpFactorPrefixProgram.grouped_lengths i.scopes i.origins i.columns heq hsize)
    simpa only [List.length_map, groups, htables] using h
  constructor
  · simpa only [factorInputs, List.map_map, Function.comp_def] using
      List.map_fst_zip hl.le
  · simpa only [factorInputs, List.map_map, Function.comp_def] using
      List.map_snd_zip hl.ge

theorem masters_streams (i : Inputs)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (htables : i.tables.length = i.scopes.length) :
    (masters i).groups = SubexpFactorPacketExecution.groupStream (factorInputs i) ∧
    (masters i).tables = SubexpFactorPacketExecution.tableStream (factorInputs i) := by
  obtain ⟨hg, ht⟩ := factorInputs_projections i heq hsize htables
  constructor
  · change Encoding.encodeList SubexpFactorPrefixProgram.groupBytes (groups i) =
      Encoding.encodeList SubexpFactorPacketLocal.groupBytes (factorInputs i)
    rw [← hg]
    exact encode_map SubexpFactorPrefixProgram.groupBytes
      SubexpFactorPacketLocal.Input.prefixes (factorInputs i)
  · simpa only [masters, encode_map, SubexpFactorPacketExecution.tableStream, id_eq] using
      congrArg (Encoding.encodeList id) ht.symm

private theorem extend_project {r R s S : ℕ} (stack : Fin s → Fin S) (register : Fin r → Fin R)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) : Function.extend stack (d.stacks ∘ stack) d.stacks = d.stacks := by
  exact congrArg StructuredProgram.State.stacks (embedState_project register stack d hr hs)

theorem packetPorts_ne_origin (j : Fin 64) : packetPorts j ≠ 227 := by
  revert j
  decide

def runtimeBound (i : Inputs) : ℕ :=
  SubexpFactorPrefixProgram.budget (i.scopes.zip (groups i)) + 1 +
    SubexpFactorPacketExecution.runtimeBound (masters i) i.cache (factorInputs i) +
    (2 * (masters i).groups.length + 3) + 1

theorem command_eval (i : Inputs) (d : Data) (ready : Ready d i)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (htables : i.tables.length = i.scopes.length)
    (hm : 0 < BinaryArithmetic.toNat i.modulus)
    (hcache : BinaryArithmetic.toNat i.modulus ≤ i.cache.length) :
    ∃ n, n + 1 ≤ runtimeBound i ∧ ∃ e : Data,
      Eval command n d e ∧
      e.stacks = Function.update (Function.update d.stacks 227 []) 225 (output i) := by
  obtain ⟨np, hnp, rp, hp⟩ := SubexpFactorPrefixProgram.program_trace
    i.origins i.columns i.scopes heq hsize (d.regs ∘ registers)
  rw [← ready.prefix_eq] at hp
  have ep := eval_call_from_state SubexpFactorPrefixProgram.program registers prefixPorts d
    registers_injective prefixPorts_injective hp
  let d1 := embedState registers prefixPorts d
    (SubexpFactorPrefixProgram.outputState rp i.origins i.columns i.scopes)
  have hpst : d1.stacks = Function.update (Function.update d.stacks 227 []) 224 (masters i).groups := by
    have hs : (SubexpFactorPrefixProgram.outputState rp i.origins i.columns i.scopes).stacks =
        Function.update (Function.update
          (SubexpFactorPrefixProgram.inputState (d.regs ∘ registers) i.origins i.columns i.scopes).stacks
            0 []) 3 (masters i).groups := by
      funext j
      fin_cases j <;> rfl
    change Function.extend prefixPorts
      (SubexpFactorPrefixProgram.outputState rp i.origins i.columns i.scopes).stacks d.stacks = _
    rw [hs, ProgramLinking.extend_update prefixPorts_injective,
      ProgramLinking.extend_update prefixPorts_injective]
    rw [← ready.prefix_eq]
    change Function.update (Function.update
      (Function.extend prefixPorts (d.stacks ∘ prefixPorts) d.stacks) (prefixPorts 0) [])
        (prefixPorts 3) (masters i).groups = _
    rw [extend_project prefixPorts registers registers_injective prefixPorts_injective]
    rfl
  have hready1 : projectState registers packetPorts d1 =
      SubexpFactorPacketControl.state (d1.regs ∘ registers) (masters i) := by
    refine SubexpScanPrimitives.state_ext (by rfl) ?_
    funext j
    have hj := congrArg (fun s : State 8 64 => s.stacks j) ready.packet_eq
    change d.stacks (packetPorts j) = SubexpFactorPacketControl.store (initialMasters i) j at hj
    change d1.stacks (packetPorts j) = SubexpFactorPacketControl.store (masters i) j
    rw [hpst]
    by_cases h41 : j = 41
    · subst j
      simp [packetPorts, SubexpFactorPacketControl.store]
    · have hn224 : packetPorts j ≠ 224 := by
        intro h
        exact h41 (packetPorts_injective (h.trans (show packetPorts 41 = 224 from rfl).symm))
      rw [Function.update_of_ne hn224, Function.update_of_ne (packetPorts_ne_origin j), hj]
      simp [initialMasters, SubexpFactorPacketControl.store, h41]
  obtain ⟨hg, ht⟩ := masters_streams i heq hsize htables
  obtain ⟨rc, nc, hnc, hc⟩ := SubexpFactorPacketExecution.program_runsIn
    (d1.regs ∘ registers) (masters i) i.cache rfl hm hcache (factorInputs i) hg ht
  rw [← hready1] at hc
  have ec := eval_call_from_state SubexpFactorPacketControl.program registers packetPorts d1
    registers_injective packetPorts_injective hc
  let d2 := embedState registers packetPorts d1
    (SubexpFactorPacketControl.outputState rc (masters i) (output i))
  have hcst : d2.stacks = Function.update d1.stacks 225 (output i) := by
    change Function.extend packetPorts
      (Function.update (SubexpFactorPacketControl.store (masters i)) 47 (output i)) d1.stacks = _
    rw [ProgramLinking.extend_update packetPorts_injective]
    have hs := congrArg StructuredProgram.State.stacks hready1
    change d1.stacks ∘ packetPorts = SubexpFactorPacketControl.store (masters i) at hs
    rw [← hs, extend_project packetPorts registers registers_injective packetPorts_injective]
    rfl
  have h224 : d2.stacks 224 = (masters i).groups := by
    rw [hcst, hpst]
    simp
  have hclear := ListRegisterProgram.clear_run (224 : Fin 288) (0 : Fin 16) 1 d2.regs d2.stacks
  let e : Data := ⟨readRegs d2.regs 0 1 none, Function.update d2.stacks 224 []⟩
  have ee : Eval cleanup (2 * (masters i).groups.length + 3) d2 e := by
    apply Eval.call
    simpa only [cleanup, h224, StackRoutines.clearStacks] using hclear
  have hinit224 : d.stacks 224 = [] := by
    have h := congrArg (fun s : State 8 24 => s.stacks 3) ready.prefix_eq
    exact h
  have hest : e.stacks = Function.update (Function.update d.stacks 227 []) 225 (output i) := by
    change Function.update d2.stacks 224 [] = _
    rw [hcst, hpst]
    funext j
    by_cases h224' : j = 224 <;> by_cases h225 : j = 225 <;> by_cases h227 : j = 227 <;>
      simp [h224', h225, h227, hinit224]
  have hall := ep.seq (ec.seq ee)
  refine ⟨np + (nc + (2 * (masters i).groups.length + 3)), ?_, e, hall, hest⟩
  unfold runtimeBound
  change np ≤ SubexpFactorPrefixProgram.budget (i.scopes.zip (groups i)) + 1 at hnp
  omega

theorem program_runsIn (i : Inputs) (d : Data) (ready : Ready d i)
    (heq : i.origins.length = i.columns.length)
    (hsize : (i.scopes.map List.length).sum = i.origins.length)
    (htables : i.tables.length = i.scopes.length)
    (hm : 0 < BinaryArithmetic.toNat i.modulus)
    (hcache : BinaryArithmetic.toNat i.modulus ≤ i.cache.length) :
    ∃ e : Data, RunsIn program (runtimeBound i)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 227 []) 225 (output i) := by
  obtain ⟨n, hn, e, he, hs⟩ := command_eval i d ready heq hsize htables hm hcache
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 102 225⟩, hs⟩

end SubexponentialSAT.SubexpFactorPacketProgram

end OAI.Algorithms
