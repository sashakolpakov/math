import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramNormalize

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev SignatureData := State 8 15
abbrev SignatureCode := Cmd 8 15

def signatureState (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) : SignatureData :=
  ⟨regs, ![W,[],[],[],[],[],[],[],[],[],[],[],bits,words (rows.map words),key]⟩

def rowCallPorts : Fin 12 → Fin 15 := Fin.castAdd 3

def rowCall : SignatureCode := .call
  (ProgramLinking.liftProgram canonicalRowProgram id rowCallPorts)

def signatureSeed : SignatureCode := .base
  (.seq (.atom (.set 0 true)) (.atom (.push 2 0)))

def signatureStep : SignatureCode :=
  .seq (readWord 13 9 11 (by decide))
    (.seq (copy 12 10 11)
      (.seq signatureSeed (.seq rowCall (emitFrame 2 14 11 (by decide)))))

def rowKey (W bits : List Bool) (row : List (List Bool)) : List Bool :=
  canonical (1+rowValue W row bits)

def signatureStepCost (W bits : List Bool) (row : List (List Bool)) : ℕ :=
  9*(words row).length+7 + (7*bits.length+5) + 2 +
    (canonicalRowBudget W row+1) + (8*(rowKey W bits row).length+8)

theorem signatureStep_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (row : List (List Bool)) (rows : List (List (List Bool))) (key : List Bool)
    (hlen : row.length=bits.length) :
    ∃ t ≤ signatureStepCost W bits row, ∃ rf,
      Eval signatureStep t (signatureState regs W bits (row::rows) key)
        (signatureState rf W bits rows (Encoding.frame (rowKey W bits row)++key)) := by
  let d := signatureState regs W bits (row::rows) key
  obtain ⟨a,hea,hsa⟩ := readWord_eval (13 : Fin 15) 9 11
    (by decide) (by decide) (by decide) d (words row) (words (rows.map words)) rfl rfl rfl
  obtain ⟨b,heb,hsb⟩ := copy_eval (12 : Fin 15) 10 11
    (by decide) (by decide) (by decide) a (by rw [hsa]; rfl)
  let c : SignatureData := ⟨Function.update b.regs 0 true, Function.update b.stacks 2 [true]⟩
  have hb2 : b.stacks 2 = [] := by rw [hsb,hsa]; rfl
  have hec : Eval signatureSeed 2 b c := by
    have h := (StructuredProgram.Eval.atom (.set (0 : Fin 8) true) b).seq
      (StructuredProgram.Eval.atom (.push (2 : Fin 15) 0) _)
    exact .base (by simpa [signatureSeed,c,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC,execInstr,hb2] using h)
  have hproj : projectState id rowCallPorts c = dotState c.regs W row bits [true] := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    fin_cases i <;> simp [rowCallPorts,c,hsb,hsa,d,signatureState,StackRoutines.copyStacks]
  obtain ⟨tc,htc,rc,hecRow⟩ := canonicalRowCommand_eval c.regs W row bits hlen
  rw [←hproj] at hecRow
  have hecall := eval_call_from_state canonicalRowProgram id rowCallPorts c
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hecRow 9 2)
  let e : SignatureData := ⟨rc, Function.update (Function.update
    (Function.update c.stacks 9 []) 10 []) 2 (rowKey W bits row)⟩
  have hembed : embedState id rowCallPorts c
      (dotState rc W [] [] (rowKey W bits row)) = e := by
    apply embedState_eq_of_ports id rowCallPorts c _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i
      fin_cases i <;> simp [e,rowCallPorts,c,hsb,hsa,d,signatureState,
        dotState,StackRoutines.copyStacks] ; rfl
    · intro i hi
      have h2 : i≠2 := fun h => hi ⟨2,h.symm⟩
      have h9 : i≠9 := fun h => hi ⟨9,h.symm⟩
      have h10 : i≠10 := fun h => hi ⟨10,h.symm⟩
      simp [e,h2,h9,h10]
  change Eval rowCall (tc+1) c (embedState id rowCallPorts c
    (dotState rc W [] [] (rowKey W bits row))) at hecall
  rw [hembed] at hecall
  obtain ⟨f,hef,hsf⟩ := emitFrame_eval (2 : Fin 15) 14 11
    (by decide) (by decide) (by decide) e (by
      simp [e,c,hsb,hsa,d,signatureState,StackRoutines.copyStacks])
  have he2 : e.stacks 2 = rowKey W bits row := by simp [e]
  have hf : f = signatureState f.regs W bits rows
      (Encoding.frame (rowKey W bits row)++key) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i
    fin_cases i <;> simp [e,c,hsb,hsa,d,signatureState,StackRoutines.copyStacks]
  have ha12 : a.stacks 12=bits := by rw [hsa]; rfl
  have he := hea.seq (heb.seq (hec.seq (hecall.seq hef)))
  rw [hf] at he
  refine ⟨_,?_,f.regs,he⟩
  rw [ha12,he2]
  dsimp [signatureStepCost]
  omega

def signaturePeek : SignatureCode := .base (.atom (.peek 13 0 1))
def signatureBody : SignatureCode := .seq signatureStep signaturePeek
def signatureLoop : SignatureCode := .while 1 signatureBody
def signatureCommand : SignatureCode := .seq signaturePeek signatureLoop

def signatureReady (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) : SignatureData :=
  signatureState (readRegs regs 0 1 (words (rows.map words)).head?) W bits rows key

def signatureValue (W bits : List Bool) (rows : List (List (List Bool))) : List Bool :=
  words ((rows.map (rowKey W bits)).reverse)

def signatureCost (W bits : List Bool) (rows : List (List (List Bool))) : ℕ :=
  ((rows.map (fun row => signatureStepCost W bits row+2)).sum)+1

theorem signaturePeek_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) :
    Eval signaturePeek 1 (signatureState regs W bits rows key)
      (signatureReady regs W bits rows key) := Eval.base (StructuredProgram.Eval.atom _ _)

theorem signatureLoop_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool)
    (hlen : ∀ row∈rows, row.length=bits.length) :
    ∃ t ≤ signatureCost W bits rows, ∃ rf,
      Eval signatureLoop t (signatureReady regs W bits rows key)
        (signatureState rf W bits [] (signatureValue W bits rows++key)) := by
  induction rows generalizing regs key with
  | nil =>
      refine ⟨1,by simp [signatureCost],(signatureReady regs W bits [] key).regs,?_⟩
      simpa [signatureLoop, signatureBody, signatureReady, signatureState,
        signatureValue, words, readRegs] using (Eval.while_false
        (show (signatureReady regs W bits [] key).regs 1=false by
          simp [signatureReady,signatureState,words,readRegs]) :
          Eval signatureLoop 1 (signatureReady regs W bits [] key)
            (signatureReady regs W bits [] key))
  | cons row rows ih =>
      obtain ⟨t,ht,rm,he⟩ := signatureStep_eval
        (signatureReady regs W bits (row::rows) key).regs W bits row rows key
        (hlen row (by simp))
      obtain ⟨u,hu,rf,hf⟩ := ih rm (Encoding.frame (rowKey W bits row)++key)
        (fun r hr => hlen r (by simp [hr]))
      have hg : (signatureReady regs W bits (row::rows) key).regs 1=true := by
        cases hr : words row <;> simp [signatureReady,signatureState,words,readRegs,
          Encoding.frame,hr]
      have h := Eval.while_true hg (he.seq (signaturePeek_eval rm W bits rows _)) hf
      refine ⟨(t+1)+u+1,?_,rf,?_⟩
      · simp only [signatureCost,List.map_cons,List.sum_cons] at *
        omega
      · simpa [signatureLoop, signatureBody, signatureValue, List.reverse_cons,
          words_append, words, List.append_assoc] using h

def signatureProgram := compiled signatureCommand 13 14

theorem signatureCommand_eval (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool)
    (hlen : ∀ row∈rows, row.length=bits.length) :
    ∃ t ≤ signatureCost W bits rows+1, ∃ rf,
      Eval signatureCommand t (signatureState regs W bits rows key)
        (signatureState rf W bits [] (signatureValue W bits rows++key)) := by
  obtain ⟨t,ht,rf,he⟩ := signatureLoop_eval regs W bits rows key hlen
  exact ⟨1+t,by omega,rf,(signaturePeek_eval regs W bits rows key).seq he⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
