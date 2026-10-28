import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExtractionJobProgram
import OAI.Algorithms.SubexponentialSAT.UnaryGridProgram
import OAI.Algorithms.SubexponentialSAT.SubexpExponentController
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpQueryOrder

namespace OAI.Algorithms

/-! The key-only version of the same degree-budget and U/Z enumeration.
It supplies the dense-arithmetic slot master without any moment source. -/

namespace SubexponentialSAT.SubexpSlotProgram

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Data := StructuredProgram.State 3 24
abbrev Code := StructuredCalls.Cmd 3 24

def keyStep (xs : List Bool) (width u z : ℕ) (out : List Bool) : List Bool :=
  true :: (Encoding.frame (SubexpExtractionJobProgram.normalizedKey xs u z width) ++ out)

def keyCost (xs : List Bool) (width u z : ℕ) : ℕ :=
  100 * (xs.length + u + z + width + 1)

def work : List (Fin 24) := [4, 5, 6, 7, 8, 9, 10, 11]

structure Prepared (d : Data) (xs : List Bool) (D width : ℕ) : Prop where
  x : d.stacks 0 = xs
  dimension : d.stacks 2 = List.replicate D true
  width : d.stacks 3 = List.replicate width true
  clean : ∀ i ∈ work, d.stacks i = []

def grid : Code := UnaryGridProgram.command SubexpExtractionJobProgram.emitKey

def gridCost (xs : List Bool) (D width : ℕ) : ℕ :=
  D * (D + 1) * (100 * (xs.length + 2 * D + width + 1)) +
    13 * D ^ 2 + 31 * D + 10

theorem grid_eval (d : Data) (xs : List Bool) (D width : ℕ)
    (h : Prepared d xs D width) :
    ∃ n e, n ≤ gridCost xs D width ∧ Eval grid n d e ∧
      e.stacks = Function.update d.stacks 14
        (UnaryGridProgram.gridOutput (keyStep xs width) D D (d.stacks 14)) := by
  have spec : UnaryGridProgram.CallbackSpec SubexpExtractionJobProgram.emitKey
      (keyStep xs width) (keyCost xs width) d := by
    intro u z a hf hu hz
    have hk : SubexpExtractionJobProgram.KeyReady a xs u z width := by
      constructor
      · exact (hf 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x
      · exact hu
      · exact hz
      · exact (hf 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.width
      · exact (hf 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (h.clean 8 (by decide))
      · exact (hf 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (h.clean 9 (by decide))
      · exact (hf 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (h.clean 10 (by decide))
      · exact (hf 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (h.clean 11 (by decide))
    exact SubexpExtractionJobProgram.emitKey_eval a xs u z width hk
  obtain ⟨costs, n, e, he, _, _, hs, hn⟩ :=
    UnaryGridProgram.grid_correct SubexpExtractionJobProgram.emitKey
      (keyStep xs width) (keyCost xs width) d spec
      (h.clean 4 (by decide)) (h.clean 5 (by decide)) (h.clean 6 (by decide))
      (h.clean 7 (by decide)) (h.clean 11 (by decide))
  have hD : (d.stacks 2).length = D := by rw [h.dimension, List.length_replicate]
  rw [hD] at hn hs
  have hb := UnaryGridProgram.gridBound_le_uniform (keyCost xs width) D
    (100 * (xs.length + 2 * D + width + 1)) (by
      intro u z hu hz
      dsimp [keyCost]
      omega)
  exact ⟨n, e, hn.trans hb, he, hs⟩

def rowKeys (xs : List Bool) (width z count : ℕ) : List (List Bool) :=
  (List.range count).map fun u => SubexpExtractionJobProgram.normalizedKey xs u z width

def keys (xs : List Bool) (D width count : ℕ) : List (List Bool) :=
  (List.range count).flatMap fun z => rowKeys xs width z (D + 1)

theorem rowOutput_keys (xs : List Bool) (width z count : ℕ) (old : List (List Bool)) :
    UnaryGridProgram.rowOutput (keyStep xs width) z count (Encoding.encodeList id old) =
      Encoding.encodeList id ((rowKeys xs width z count).reverse ++ old) := by
  induction count with
  | zero => simp [UnaryGridProgram.rowOutput, rowKeys]
  | succ count ih =>
    simp [UnaryGridProgram.rowOutput, ih, keyStep, rowKeys, List.range_succ,
      List.reverse_append, Encoding.encodeList]

theorem gridOutput_keys (xs : List Bool) (D width count : ℕ) (old : List (List Bool)) :
    UnaryGridProgram.gridOutput (keyStep xs width) D count (Encoding.encodeList id old) =
      Encoding.encodeList id ((keys xs D width count).reverse ++ old) := by
  induction count with
  | zero => simp [UnaryGridProgram.gridOutput, keys]
  | succ count ih =>
    rw [UnaryGridProgram.gridOutput, ih, rowOutput_keys]
    simp [keys, List.range_succ, List.flatMap_append, List.reverse_append, List.append_assoc]

theorem keys_length (xs : List Bool) (D width count : ℕ) :
    (keys xs D width count).length = count * (D + 1) := by
  simp [keys, rowKeys, List.length_flatMap]

theorem keys_fixedKey {D : ℕ} (a : Fin D → ℕ) (ha : ∑ i, a i ≤ 2 * D + 1) :
    keys (SubexpExponentController.momentWord a) D (SubexpSymbolicCost.indexBits D) D =
      (List.range D).flatMap (fun z => (List.range (D + 1)).map fun u =>
        SubexpSymbolicCost.fixedKey (a, u, z)) := by
  unfold keys
  apply List.flatMap_congr
  intro z hz
  unfold rowKeys
  apply List.map_congr_left
  intro u hu
  exact SubexpExtractionJobProgram.normalizedKey_eq_fixedKey a u z
    ⟨ha, List.mem_range.mp hu, List.mem_range.mp hz⟩

def ports : RecordPrograms.Ports 3 24 where
  tag := 0
  present := 1
  found := 2
  source := 20
  payload := 21
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def moveX : Code := .call (StackRoutines.transferProgram 21 0 0 1)
def movedX (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 21 0 d.stacks⟩

theorem moveX_eval (d : Data) :
    Eval moveX (3 * (d.stacks 21).length + 3) d (movedX d) := by
  apply Eval.call
  exact ListRegisterProgram.transfer_run 21 0 0 1 (by decide) (by decide) d.regs d.stacks

def reset : Code := .base (.seq (.atom (.set 0 false))
  (.seq (.atom (.set 1 true)) (.atom (.set 2 false))))

def resetState (d : Data) : Data := ⟨![false, true, false], d.stacks⟩

theorem reset_eval (d : Data) : Eval reset 3 d (resetState d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) d).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) true) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  have hr : Function.update (Function.update (Function.update d.regs 0 false) 1 true) 2 false =
      ![false, true, false] := by funext i; fin_cases i <;> simp
  exact .base (by simpa [resetState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr, hr] using h)

def callback : Code := .seq moveX (.seq grid (.seq (UnaryGridProgram.clear 0) reset))
def command : Code := RecordPrograms.iterate ports callback
def program := StructuredCalls.compiled command 20 14

def Frame (context d : Data) : Prop :=
  ∀ i : Fin 24, i ≠ 0 → i ≠ 14 → i ≠ 20 → i ≠ 21 → d.stacks i = context.stacks i

structure Invariant (context d : Data) : Prop where
  frame : Frame context d
  xEmpty : d.stacks 0 = []

structure Context (context : Data) (D width : ℕ) : Prop where
  dimension : context.stacks 2 = List.replicate D true
  width : context.stacks 3 = List.replicate width true
  clean : ∀ i ∈ work, context.stacks i = []

def outputStep (D width : ℕ) (xs out : List Bool) : List Bool :=
  UnaryGridProgram.gridOutput (keyStep xs width) D D out

def callbackCost (D width : ℕ) (xs : List Bool) : ℕ := gridCost xs D width + 5 * xs.length + 9

theorem callback_contract (context : Data) (D width : ℕ) (hc : Context context D width) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost D width) (Invariant context)
      (fun bits a b => b.stacks 14 = outputStep D width bits (a.stacks 14)) := by
  intro bits tail base hi
  let a := RecordPrograms.state ports base false true false tail bits.reverse
  let b := movedX a
  have hb0 : b.stacks 0 = bits := by
    simp [b, a, movedX, StackRoutines.transferStacks, RecordPrograms.state, ports, hi.xEmpty]
  have hbFrame : Frame context b := by
    intro i h0 h14 h20 h21
    simpa [b, a, movedX, StackRoutines.transferStacks, RecordPrograms.state, ports,
      h0, h20, h21] using hi.frame i h0 h14 h20 h21
  have hbPrepared : Prepared b bits D width := by
    constructor
    · exact hb0
    · exact (hbFrame 2 (by decide) (by decide) (by decide) (by decide)).trans hc.dimension
    · exact (hbFrame 3 (by decide) (by decide) (by decide) (by decide)).trans hc.width
    · intro i himem
      have hne : i ≠ 0 ∧ i ≠ 14 ∧ i ≠ 20 ∧ i ≠ 21 := by
        simp only [work, List.mem_cons, List.not_mem_nil, or_false] at himem
        rcases himem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hbFrame i hne.1 hne.2.1 hne.2.2.1 hne.2.2.2).trans (hc.clean i himem)
  obtain ⟨gn, g, hgn, hg, hgs⟩ := grid_eval b bits D width hbPrepared
  let e := resetState (UnaryGridProgram.cleared 0 g)
  have heFrame : Frame context e := by
    intro i h0 h14 h20 h21
    simpa [e, resetState, UnaryGridProgram.cleared, hgs, h0, h14] using
      hbFrame i h0 h14 h20 h21
  have he0 : e.stacks 0 = [] := by simp [e, resetState, UnaryGridProgram.cleared]
  have he20 : e.stacks 20 = tail := by
    simp [e, resetState, UnaryGridProgram.cleared, hgs, b, a, movedX,
      StackRoutines.transferStacks, RecordPrograms.state, ports]
  have he21 : e.stacks 21 = [] := by
    simp [e, resetState, UnaryGridProgram.cleared, hgs, b, movedX, StackRoutines.transferStacks]
  have heState : RecordPrograms.state ports e false true false tail [] = e := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · exact he20
    · exact he21
  have hrun := (moveX_eval a).seq (hg.seq
    ((UnaryGridProgram.clear_eval 0 g).seq (reset_eval (UnaryGridProgram.cleared 0 g))))
  refine ⟨3 * (a.stacks 21).length + 3 + (gn + (2 * (g.stacks 0).length + 3 + 3)),
    e, ?_, ⟨heFrame, he0⟩, ?_, ?_⟩
  · have hgl : (g.stacks 0).length = bits.length := by simp [hgs, hb0]
    have hal : (a.stacks 21).length = bits.length := by simp [a, RecordPrograms.state, ports]
    change (3 * (a.stacks 21).length + 3) + (gn + (2 * (g.stacks 0).length + 3 + 3)) ≤ _
    rw [hgl, hal]
    dsimp [callbackCost]
    omega
  · simp [e, resetState, UnaryGridProgram.cleared, hgs, b, a, movedX,
      StackRoutines.transferStacks, RecordPrograms.state, ports, outputStep]
  · rw [heState]
    exact hrun

def allKeys (D width : ℕ) (records : List (List Bool)) : List (List Bool) :=
  records.flatMap fun xs => keys xs D width D

theorem fold_keys (D width : ℕ) (records old : List (List Bool)) :
    records.foldl (fun out xs => outputStep D width xs out) (Encoding.encodeList id old) =
      Encoding.encodeList id ((allKeys D width records).reverse ++ old) := by
  induction records generalizing old with
  | nil => simp [allKeys]
  | cons xs rest ih =>
    rw [List.foldl_cons, outputStep, gridOutput_keys, ih]
    simp [allKeys, List.reverse_append, List.append_assoc]

theorem allKeys_length (D width : ℕ) (records : List (List Bool)) :
    (allKeys D width records).length = records.length * (D * (D + 1)) := by
  simp [allKeys, List.length_flatMap, keys_length]

theorem program_runs (context : Data) (D width : ℕ) (hc : Context context D width)
    (records : List (List Bool)) (base : Data) (hi : Invariant context base)
    (old : List (List Bool)) (hout : base.stacks 14 = Encoding.encodeList id old) :
    ∃ e : Data, RunsIn program (4 + RecordPrograms.budget (callbackCost D width) records)
      ((RecordPrograms.state ports base false false false (Encoding.encodeList id records) []).withPC
        (some program.entry))
      ((RecordPrograms.state ports e false true false [] []).withPC none) ∧
      Invariant context e ∧
      e.stacks 14 = Encoding.encodeList id ((allKeys D width records).reverse ++ old) := by
  obtain ⟨n, e, hn, he, hv, hr⟩ := RecordPrograms.iterate_run_with ports callback (fun _ => false)
    (callbackCost D width) (Invariant context)
    (fun xs a b => b.stacks 14 = outputStep D width xs (a.stacks 14))
    (callback_contract context D width hc) records [] base hi false false false
  have hfold := hv.fold_of_false (by intros; rfl) (fun d => d.stacks 14)
    (fun out xs => outputStep D width xs out) (by intros; assumption)
  rw [hout, fold_keys] at hfold
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  refine ⟨e, ⟨n + 1, by omega, ?_⟩, he, hfold⟩
  have ht := StructuredCalls.compiled_halt_trace hr 20 14
  simpa [program, command, hany, SubexpNormalizeProgram.unread_false] using ht

def momentRecords (D : ℕ) : List (List Bool) :=
  (Algorithm.exponentList D (2 * D + 1)).reverse.map SubexpExponentController.momentWord

/-- This is the forward visit order. The emitted slot master reverses it,
exactly as required by the dense projection loop. -/
def slots (D : ℕ) : List (SymbolicCost.RawIndex D) :=
  (Algorithm.exponentList D (2 * D + 1)).reverse.flatMap fun a =>
    (List.range D).flatMap fun z => (List.range (D + 1)).map fun u => (a, u, z)

theorem slots_eq_visitSlots (D : ℕ) : slots D = SubexpQueryOrder.visitSlots D := rfl

theorem slots_perm (D : ℕ) : (slots D).Perm (Algorithm.retainedSlots D) :=
  SubexpQueryOrder.visitSlots_perm D

theorem slots_nodup (D : ℕ) : (slots D).Nodup := SubexpQueryOrder.visitSlots_nodup D

theorem mem_slots (D : ℕ) (s : SymbolicCost.RawIndex D) :
    s ∈ slots D ↔ SymbolicCost.Retained D s := SubexpQueryOrder.mem_visitSlots D s

theorem momentRecords_encode (D : ℕ) :
    Encoding.encodeList id (momentRecords D) =
      Encoding.encodeList SubexpExponentController.momentWord
        (Algorithm.exponentList D (2 * D + 1)).reverse := by
  have h : ∀ xs : List (Fin D → ℕ),
      Encoding.encodeList id (xs.map SubexpExponentController.momentWord) =
        Encoding.encodeList SubexpExponentController.momentWord xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [Encoding.encodeList, ih]
  exact h _

theorem allKeys_moments (D : ℕ) :
    allKeys D (SubexpSymbolicCost.indexBits D) (momentRecords D) =
      (slots D).map SubexpSymbolicCost.fixedKey := by
  simp only [allKeys, momentRecords, slots, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hsum := (Algorithm.mem_exponentList D (2 * D + 1) a).mp (List.mem_reverse.mp ha)
  simpa only [List.map_flatMap, List.map_map, Function.comp_def] using keys_fixedKey a hsum

theorem slots_retained (D : ℕ) (s : SymbolicCost.RawIndex D) (h : s ∈ slots D) :
    SymbolicCost.Retained D s := by
  rcases List.mem_flatMap.mp h with ⟨a, ha, hs⟩
  rcases List.mem_flatMap.mp hs with ⟨z, hz, hs⟩
  rcases List.mem_map.mp hs with ⟨u, hu, rfl⟩
  exact ⟨(Algorithm.mem_exponentList D (2 * D + 1) a).mp (List.mem_reverse.mp ha),
    List.mem_range.mp hu, List.mem_range.mp hz⟩

theorem slots_length (D : ℕ) :
    (slots D).length = (3 * D + 1).choose D * (D * (D + 1)) := by
  have h := congrArg List.length (allKeys_moments D)
  rw [allKeys_length, List.length_map] at h
  rw [← h]
  simp only [momentRecords, List.length_map, List.length_reverse, Algorithm.exponentList_length]
  congr 2
  omega

theorem moments_program_runs (context : Data) (D : ℕ)
    (hc : Context context D (SubexpSymbolicCost.indexBits D))
    (base : Data) (hi : Invariant context base) (hout : base.stacks 14 = [false]) :
    ∃ e : Data, RunsIn program
      (4 + RecordPrograms.budget (callbackCost D (SubexpSymbolicCost.indexBits D)) (momentRecords D))
      ((RecordPrograms.state ports base false false false
        (Encoding.encodeList id (momentRecords D)) []).withPC (some program.entry))
      ((RecordPrograms.state ports e false true false [] []).withPC none) ∧
      Invariant context e ∧
      e.stacks 14 = Encoding.encodeList id ((slots D).map SubexpSymbolicCost.fixedKey).reverse := by
  obtain ⟨e, he, hi', hs⟩ := program_runs context D (SubexpSymbolicCost.indexBits D) hc
    (momentRecords D) base hi [] hout
  rw [allKeys_moments, List.append_nil] at hs
  exact ⟨e, he, hi', hs⟩

end SubexponentialSAT.SubexpSlotProgram

end OAI.Algorithms
