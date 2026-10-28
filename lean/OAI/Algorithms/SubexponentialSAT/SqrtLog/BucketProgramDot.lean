import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramArithmetic
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual row-entry parsing, assignment-bit scanning, binary addition and
workspace recycling for one exact offset-signature row. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev DotData := State 8 12
abbrev DotCode := Cmd 8 12

def dotState (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) : DotData :=
  ⟨regs, ![W, [], acc, [], [], [], [], [], [], words coeffs, bits, []]⟩

def choicePort : Fin 9 → Fin 12 := Fin.castAdd 3

theorem choicePort_injective : Function.Injective choicePort := Fin.castAdd_injective _ _

def choiceCall : DotCode := .call (ProgramLinking.liftProgram choiceAddProgram id choicePort)

def addView (d : DotData) : AddData := projectState id choicePort d

theorem choiceCall_eval (d : DotData) (hd : addReady (addView d)) :
    ∃ t ≤ 100*(addInputLength (addView d)+1)^2+2, ∃ rf word,
      Eval choiceCall t d ⟨rf, Function.update d.stacks 3 word⟩ ∧
      SubexponentialSAT.BinaryArithmetic.toNat word = SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2) +
        (if d.regs 0 then SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1)
         else SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0)) ∧
      word.length ≤ addInputLength (addView d)+1 := by
  obtain ⟨t, ht, rf, word, he, hv, hl⟩ := choiceAdd_eval (addView d) hd
  have hp : projectState id choicePort d = addView d := rfl
  have he' := eval_call_from_state choiceAddProgram id choicePort d
    Function.injective_id choicePort_injective (compiled_halt_trace he 0 3)
  have hend : embedState id choicePort d ⟨rf, Function.update (addView d).stacks 3 word⟩ =
      (⟨rf, Function.update d.stacks 3 word⟩ : DotData) := by
    apply embedState_eq_of_ports id choicePort d _ _ Function.injective_id choicePort_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
      simp [h3]
  rw [hend] at he'
  exact ⟨t+1, by omega, rf, word, he', hv, hl⟩

def popAssignment : DotCode := .base (.atom (.pop 10 0 1))

def dotStep : DotCode :=
  .seq (readWord 9 1 11 (by decide))
    (.seq popAssignment
      (.seq choiceCall
        (.seq (WorkspaceCleanupProgram.command 0 1 [1, 2]) (move 3 2 11))))

def dotStepBound (W coeff acc : List Bool) : ℕ :=
  200*(W.length+coeff.length+acc.length+2)^2+30

theorem dotStep_eval (regs : Fin 8 → Bool) (W coeff : List Bool)
    (coeffs : List (List Bool)) (bit : Bool) (bits acc : List Bool) :
    ∃ t ≤ dotStepBound W coeff acc, ∃ rf out,
      Eval dotStep t (dotState regs W (coeff::coeffs) (bit::bits) acc)
        (dotState rf W coeffs bits out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc +
        (if bit then SubexponentialSAT.BinaryArithmetic.toNat coeff else SubexponentialSAT.BinaryArithmetic.toNat W) ∧
      out.length ≤ W.length+coeff.length+acc.length+1 := by
  let d := dotState regs W (coeff::coeffs) (bit::bits) acc
  obtain ⟨a, hea, hsa⟩ := readWord_eval (9 : Fin 12) 1 11
    (by decide) (by decide) (by decide) d coeff (words coeffs) rfl rfl rfl
  let b : DotData := ⟨readRegs a.regs 0 1 (some bit), Function.update a.stacks 10 bits⟩
  have hpop : Eval popAssignment 1 a b := by
    have ha10 : a.stacks 10 = bit::bits := by rw [hsa]; rfl
    have he := Eval.base (StructuredProgram.Eval.atom
      (StructuredProgram.Atom.pop (10 : Fin 12) (0 : Fin 8) 1) a)
    simpa [popAssignment, b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, ha10] using he
  have hb (i : Fin 12) : b.stacks i =
      (Function.update (Function.update (Function.update d.stacks 9 (words coeffs)) 1 coeff) 10 bits) i := by
    simp [b, hsa]
  have hready : addReady (addView b) := by
    constructor
    · rw [show (addView b).stacks 3 = b.stacks 3 from rfl, hb]; rfl
    · intro i; fin_cases i <;> simp [addView, projectState, choicePort, addWork, b, hsa, d, dotState] <;> rfl
  obtain ⟨tc, htc, rc, out, hec, hvc, hlc⟩ := choiceCall_eval b hready
  let c : DotData := ⟨rc, Function.update b.stacks 3 out⟩
  let e := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([1,2] : List (Fin 12)) c
  have heclean := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([1,2] : List (Fin 12)) (by decide) c
  obtain ⟨f, hef, hsf⟩ := move_eval (3 : Fin 12) 2 11
    (by decide) (by decide) (by decide) e (by simp [e]) (by simp [e,c,hb,d,dotState])
  have hf : f = dotState f.regs W coeffs bits out := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i
    fin_cases i <;> simp [e, c, hb, d, dotState]
  have hlen : addInputLength (addView b) = W.length+coeff.length+acc.length := by
    simp [addInputLength, addView, projectState, choicePort, hb, d, dotState]
  have hvalue : SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc +
      (if bit then SubexponentialSAT.BinaryArithmetic.toNat coeff else SubexponentialSAT.BinaryArithmetic.toNat W) := by
    simpa [b, hsa, d, dotState, readRegs] using hvc
  have he3 : e.stacks 3 = out := by simp [e,c]
  have hcleanCost : WorkspaceCleanupProgram.cost ([1,2] : List (Fin 12)) c =
      2*(coeff.length+acc.length)+6 := by
    simp [WorkspaceCleanupProgram.cost, c, hb, d, dotState]
  have he := hea.seq (hpop.seq (hec.seq (heclean.seq hef)))
  rw [hf] at he
  refine ⟨_, ?_, f.regs, out, he, hvalue, ?_⟩
  · rw [hcleanCost, he3]
    rw [hlen] at htc hlc
    dsimp [dotStepBound]
    nlinarith [Nat.zero_le W.length, Nat.zero_le coeff.length, Nat.zero_le acc.length]
  · simpa [hlen] using hlc

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
