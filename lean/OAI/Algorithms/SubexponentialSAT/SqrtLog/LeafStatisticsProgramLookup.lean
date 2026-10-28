import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed native bit lookup at a unary index. The mask source is preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 5
abbrev Code := Cmd 4 5
abbrev unary (n : ℕ) := List.replicate n true

abbrev state (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) : Data :=
  ⟨r, ![mask,index,scan,tmp,saved]⟩
abbrev popIndex : Code := .base (.atom (.pop 1 0 1))
abbrev popScan : Code := .base (.atom (.pop 2 2 3))
abbrev body : Code := .seq popScan popIndex
abbrev loop : Code := .while 1 body
abbrev skip : Code := .seq popIndex loop

abbrev popped (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) : Data :=
  state (readRegs r 0 1 index.head?) mask index.tail scan tmp saved

theorem popIndex_eval (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) :
    Eval popIndex 1 (state r mask index scan tmp saved)
      (popped r mask index scan tmp saved) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 5) 0 1)
    (state r mask index scan tmp saved))) using 1
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> rfl

theorem popScan_eval (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) :
    Eval popScan 1 (state r mask index scan tmp saved)
      (state (readRegs r 2 3 scan.head?) mask index scan.tail tmp saved) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 5) 2 3)
    (state r mask index scan tmp saved))) using 1
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> rfl

theorem loop_eval (r : Fin 4 → Bool) (mask before after tmp saved : List Bool) :
    ∃ rf, Eval loop (3 * before.length + 1)
      (popped r mask (unary before.length) (before ++ after) tmp saved)
      (state rf mask [] after tmp saved) := by
  induction before generalizing r with
  | nil =>
      exact ⟨readRegs r 0 1 none, Eval.while_false (by rfl)⟩
  | cons b before ih =>
      let r1 := readRegs r 0 1 (some true)
      let r2 := readRegs r1 2 3 (some b)
      obtain ⟨rf, he⟩ := ih r2
      refine ⟨rf, ?_⟩
      have hb : Eval body 2
          (popped r mask (unary (b::before).length) ((b::before) ++ after) tmp saved)
          (popped r2 mask (unary before.length) (before ++ after) tmp saved) := by
        exact (popScan_eval r1 mask (unary before.length) (b::(before++after)) tmp saved).seq
          (popIndex_eval r2 mask (unary before.length) (before++after) tmp saved)
      have hh := Eval.while_true (show
        (popped r mask (unary (b::before).length) ((b::before) ++ after) tmp saved).regs 1 = true by rfl) hb he
      convert hh using 1 ; simp [List.length_cons] ; omega

theorem skip_eval (r : Fin 4 → Bool) (mask before after tmp saved : List Bool) :
    ∃ rf, Eval skip (3 * before.length + 2)
      (state r mask (unary before.length) (before ++ after) tmp saved)
      (state rf mask [] after tmp saved) := by
  obtain ⟨rf, he⟩ := loop_eval r mask before after tmp saved
  refine ⟨rf, ?_⟩
  convert (popIndex_eval r mask (unary before.length) (before++after) tmp saved).seq he using 1 ; omega

abbrev copy : Code := .call (StackRoutines.copyProgram 0 2 3 0 1)
abbrev clear : Code := .call (StackRoutines.clearProgram 2 0 1)
abbrev command : Code := .seq copy (.seq skip (.seq popScan clear))

theorem copy_eval (r : Fin 4 → Bool) (mask index saved : List Bool) :
    Eval copy (7 * mask.length + 5) (state r mask index [] [] saved)
      (state (readRegs r 0 1 none) mask index mask [] saved) := by
  apply Eval.call
  convert (ListRegisterProgram.copy_run (0 : Fin 5) 2 3 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) r
    (state r mask index [] [] saved).stacks (by rfl)) using 1
  · simp []
  · change Cfg.mk none _ _ = Cfg.mk none _ _
    congr 1
    funext i; fin_cases i <;> simp [ StackRoutines.copyStacks]

theorem clear_eval (r : Fin 4 → Bool) (mask scan saved : List Bool) :
    Eval clear (2 * scan.length + 3) (state r mask [] scan [] saved)
      (state (readRegs r 0 1 none) mask [] [] [] saved) := by
  have h := StackRoutines.clearProgram_trace (2 : Fin 5) (0 : Fin 4) 1 r
    (state r mask [] scan [] saved).stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  convert hh using 1
  · simp []
  · simp [ StackRoutines.clearResult,
      StackRoutines.clearStacks, StructuredProgram.State.withPC ]
    funext i; fin_cases i <;> rfl

theorem command_eval (r : Fin 4 → Bool) (before after saved : List Bool) (bit : Bool) :
    ∃ rf, rf 2 = bit ∧ Eval command
      (7 * (before.length + 1 + after.length) + 3 * before.length + 2 * after.length + 11)
      (state r (before ++ bit::after) (unary before.length) [] [] saved)
      (state rf (before ++ bit::after) [] [] [] saved) := by
  let mask := before ++ bit::after
  let r1 := readRegs r 0 1 none
  obtain ⟨r2, hs⟩ := skip_eval r1 mask before (bit::after) [] saved
  let r3 := readRegs r2 2 3 (some bit)
  let rf := readRegs r3 0 1 none
  refine ⟨rf, by simp [rf,r3,readRegs], ?_⟩
  have h := (copy_eval r mask (unary before.length) saved).seq
    (hs.seq ((popScan_eval r2 mask [] (bit::after) [] saved).seq (clear_eval r3 mask after saved)))
  convert h using 1 ; simp [mask,List.length_append,List.length_cons] ; omega

abbrev program := compiled command 0 2

theorem program_runsIn (r : Fin 4 → Bool) (before after saved : List Bool) (bit : Bool) :
    ∃ rf, rf 2 = bit ∧ RunsIn program
      (12 * (before.length + 1 + after.length) + 12)
      ((state r (before ++ bit::after) (unary before.length) [] [] saved).withPC (some program.entry))
      ((state rf (before ++ bit::after) [] [] [] saved).withPC none) := by
  obtain ⟨rf,hb,he⟩ := command_eval r before after saved bit
  exact ⟨rf,hb,_,by omega,compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup

end OAI.Algorithms
