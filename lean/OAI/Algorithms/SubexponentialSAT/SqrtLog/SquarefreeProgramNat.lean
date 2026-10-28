import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramSupport
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A fixed primitive unary-field reader used by encoded sparse-key joins.
The unary magnitude affects execution time, never the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def natRegs : Fin 2 → Fin 5 := Fin.castAdd 3
def natPorts {s : ℕ} (src dst : Fin s) : Fin 2 → Fin s := ParserProgram.pair src dst

theorem natRegs_injective : Function.Injective natRegs := Fin.castAdd_injective _ _
theorem natPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (natPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [natPorts, ParserProgram.pair]

abbrev readNat {s : ℕ} (src dst : Fin s) : Cmd 5 s :=
  .call (ProgramLinking.liftProgram ParserProgram.natProgram natRegs (natPorts src dst))

def afterNat {s : ℕ} (d : State 5 s) (src dst : Fin s) (n : ℕ) (rest : List Bool) : State 5 s :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst
      (List.replicate n true ++ d.stacks dst)⟩

theorem readNat_eval {s : ℕ} (d : State 5 s) (src dst : Fin s) (hsd : src ≠ dst)
    (n : ℕ) (rest : List Bool) (hin : d.stacks src = Encoding.encodeNat n ++ rest) :
    Eval (readNat src dst) (4 * n + 4) d (afterNat d src dst n rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.encodeNat n ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (List.replicate n true ++ d.stacks dst)⟩
  have ha : embedState natRegs (natPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ natRegs_injective (natPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState natRegs (natPorts src dst) d b = afterNat d src dst n rest := by
    apply embedState_eq_of_ports _ _ _ _ _ natRegs_injective (natPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterNat, natRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [natRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [natRegs] using h.symm⟩
      simp [afterNat, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterNat, natPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [natPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [natPorts] using h.symm⟩
      simp [afterNat, hsrc, hdst]
  have ht : Trace ParserProgram.natProgram (4 * n + 4)
      (a.withPC (some ParserProgram.natProgram.entry)) (b.withPC none) :=
    ParserProgram.nat_trace n rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.natProgram natRegs
    (natPorts src dst) d natRegs_injective (natPorts_injective src dst hsd) ht
  simpa only [ha,hb,readNat] using h

abbrev joinNat : Cmd 5 3 :=
  .seq (readNat 0 2) (.seq (readNat 1 2) (.base (.atom (.push 2 0))))

theorem joinNat_eval (regs : Fin 5 → Bool) (a b : ℕ) (left right output : List Bool) :
    ∃ final, Eval joinNat (4 * (a + b) + 9)
      (maskData regs (Encoding.encodeNat a ++ left) (Encoding.encodeNat b ++ right) output)
      (maskData final left right ((Encoding.encodeNat (a+b)).reverse ++ output)) := by
  let r1 := readRegs regs (0 : Fin 5) 1 (some false)
  let r2 := readRegs r1 (0 : Fin 5) 1 (some false)
  have h1 := readNat_eval
    (maskData regs (Encoding.encodeNat a ++ left) (Encoding.encodeNat b ++ right) output)
    0 2 (by decide) a left rfl
  have h1' : Eval (readNat 0 2) (4*a+4)
      (maskData regs (Encoding.encodeNat a ++ left) (Encoding.encodeNat b ++ right) output)
      (maskData r1 left (Encoding.encodeNat b ++ right) (List.replicate a true ++ output)) := by
    convert h1 using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [maskData]
  have h2 := readNat_eval
    (maskData r1 left (Encoding.encodeNat b ++ right) (List.replicate a true ++ output))
    1 2 (by decide) b right rfl
  have h2' : Eval (readNat 1 2) (4*b+4)
      (maskData r1 left (Encoding.encodeNat b ++ right) (List.replicate a true ++ output))
      (maskData r2 left right (List.replicate b true ++ (List.replicate a true ++ output))) := by
    convert h2 using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [maskData]
  let d := maskData r2 left right (List.replicate b true ++ (List.replicate a true ++ output))
  have h3 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (2 : Fin 3) (0 : Fin 5)) d)
  have hu : (Encoding.encodeNat (a+b)).reverse ++ output =
      false :: (List.replicate b true ++ (List.replicate a true ++ output)) := by
    simp only [Encoding.encodeNat,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.reverse_replicate,List.singleton_append]
    rw [Nat.add_comm a b, List.replicate_add]
    simp only [List.cons_append,List.append_assoc]
  have h3' : Eval (.base (.atom (.push 2 0))) 1 d
      (maskData r2 left right ((Encoding.encodeNat (a+b)).reverse ++ output)) := by
    rw [hu]
    convert h3 using 1
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [d,maskData,StructuredProgram.Atom.instr,execInstr,r2,readRegs
          ]
  refine ⟨r2,?_⟩
  have ht : (4*a+4)+((4*b+4)+1) = 4*(a+b)+9 := by omega
  have he := h1'.seq (h2'.seq h3')
  rw [ht] at he
  exact he

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
