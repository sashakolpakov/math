import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Preserving binary comparison for filtering the shortened code's columns.
The instruction table uses padding and borrow, with no numeric comparison
primitive and no traversal of the original column universe. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic
open SubexponentialSAT.SaturatingSubtractionProgram

abbrev core : Cmd 8 8 :=
  .seq prepare (.seq (padAt leftPorts) (.seq (padAt rightPorts)
    (.seq setBorrow (subtractAt subtractPorts))))

theorem core_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf word, Eval core (50*(xs.length+ys.length)+49)
      (state regs xs ys []) (state rf xs ys word) ∧
      (rf 0=true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) ∧ word.length=xs.length+ys.length := by
  let shape := xs ++ ys
  let px := padTo shape xs
  let py := padTo shape ys
  have hx : xs.length ≤ shape.length := by simp [shape]
  have hy : ys.length ≤ shape.length := by simp [shape]
  have hlen : px.length = py.length := by simp [px, py, padTo_length]
  let a := store (readRegs regs 0 1 none) xs ys shape shape xs ys []
  obtain ⟨r₁, hp₁⟩ := padAt_eval leftPorts leftPorts_injective a (by rfl) hx
  let b := store r₁ xs ys px shape [] ys []
  have eb : three a r₁ leftPorts (padTo (a.stacks (leftPorts 0))
      (a.stacks (leftPorts 1))) [] [] = b := by
    apply congrArg (StructuredProgram.State.mk r₁)
    funext i
    fin_cases i <;> simp [ a, leftPorts, px]
  rw [eb] at hp₁
  obtain ⟨r₂, hp₂⟩ := padAt_eval rightPorts rightPorts_injective b (by rfl) hy
  let c := store r₂ xs ys px py [] [] []
  have ec : three b r₂ rightPorts (padTo (b.stacks (rightPorts 0))
      (b.stacks (rightPorts 1))) [] [] = c := by
    apply congrArg (StructuredProgram.State.mk r₂)
    funext i
    fin_cases i <;> simp [ b, rightPorts, py]
  rw [ec] at hp₂
  let d := store (Function.update r₂ 0 false) xs ys px py [] [] []
  have hs : Eval setBorrow 1 c d := .base (.atom _ _)
  obtain ⟨r₃, hd, hb⟩ := subtractAt_eval subtractPorts subtractPorts_injective d
    (by rfl) (by simp [d ]) hlen
  let diff := (subCarry false px py).1
  have ee : three d r₃ subtractPorts (subCarry false (d.stacks (subtractPorts 0))
      (d.stacks (subtractPorts 1))).1 [] [] = state r₃ xs ys diff := by
    apply congrArg (StructuredProgram.State.mk r₃)
    funext i
    fin_cases i <;> simp [ d, subtractPorts, diff]
  rw [ee] at hd
  change r₃ 0 = (subCarry false px py).2 at hb
  refine ⟨r₃,diff,?_,?_,?_⟩
  · have he := (prepare_eval regs xs ys).seq (hp₁.seq (hp₂.seq (hs.seq hd)))
    convert he using 1
    simp [a,b,d,px,py,shape,leftPorts,rightPorts,subtractPorts,padTo_length]
    omega
  · rw [hb,subCarry_borrow_iff px py hlen,padTo_correct shape xs hx,padTo_correct shape ys hy]
  · exact (subCarry_length false px py hlen).trans (by simp [px,shape,padTo_length])

abbrev command : Cmd 8 8 :=
  .seq core (.seq (.base (.atom (.copy 7 0))) clearOutput)
abbrev program := compiled command 0 1

theorem command_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf, Eval command (52*(xs.length+ys.length)+53)
      (state regs xs ys []) (state rf xs ys []) ∧
      (rf 7=true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rr,word,he,hflag,hwidth⟩ := core_eval regs xs ys
  let r1 := Function.update rr 7 (rr 0)
  have hsave : Eval (.base (.atom (.copy 7 0))) 1
      (state rr xs ys word) (state r1 xs ys word) := .base (.atom _ _)
  have hclear := Subexp.TupleProgram.clear_eval (2 : Fin 8) (0 : Fin 8) 1
    (state r1 xs ys word)
  let rf := readRegs r1 0 1 none
  have hfinal : (⟨rf,StackRoutines.clearStacks 2 (state r1 xs ys word).stacks⟩ : State 8 8)=
      state rf xs ys [] := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks]
  change Eval clearOutput (2*word.length+3) (state r1 xs ys word)
    ⟨rf,StackRoutines.clearStacks 2 (state r1 xs ys word).stacks⟩ at hclear
  rw [hfinal] at hclear
  refine ⟨rf,?_,?_⟩
  · convert he.seq (hsave.seq hclear) using 1
    omega
  · simpa [rf,r1,readRegs] using hflag

theorem program_runsIn (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf, RunsIn program (52*(xs.length+ys.length)+54)
      ((state regs xs ys []).withPC (some program.entry)) ((state rf xs ys []).withPC none) ∧
      (rf 7=true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rf,he,hf⟩ := command_eval regs xs ys
  exact ⟨rf,⟨_,le_rfl,by simpa using compiled_halt_trace he 0 1⟩,hf⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare

end OAI.Algorithms
