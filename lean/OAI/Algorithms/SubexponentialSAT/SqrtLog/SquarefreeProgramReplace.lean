import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramPrepend

namespace OAI.Algorithms

/-! Actual dictionary replacement: delete all old matching keys, then prepend
one supplied coefficient. This is the storage phase of additive insertion;
the coefficient addition itself is a separately measured ring operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ReplaceData := State 5 8

def keepCoefficient (d : StorageData) (coeff : List Bool) : ReplaceData :=
  ⟨d.regs, ![d.stacks 0,d.stacks 1,d.stacks 2,d.stacks 3,d.stacks 4,d.stacks 5,d.stacks 6,coeff]⟩

theorem embedSeven (a b : StorageData) (coeff : List Bool) :
    embedState id Fin.castSucc (keepCoefficient a coeff) b = keepCoefficient b coeff := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (Fin.castSucc_injective 7)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hnot : ¬ i.val < 7 := by
      intro hil
      exact hi ⟨⟨i.val,hil⟩,Fin.ext rfl⟩
    have hv : i.val = 7 := by have := i.isLt; omega
    have he : i = (7 : Fin 8) := Fin.ext hv
    subst i; rfl

def replaceRegPorts : Fin 3 → Fin 5 := Fin.castAdd 2
def replaceStackPorts : Fin 3 → Fin 8 := ![2,7,5]

theorem replaceRegPorts_injective : Function.Injective replaceRegPorts := Fin.castAdd_injective _ _
theorem replaceStackPorts_injective : Function.Injective replaceStackPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [replaceStackPorts]

def replaceData (regs : Fin 5 → Bool) (entries : List ByteRecord) (query coeff : List Bool) : ReplaceData :=
  keepCoefficient (eraseData regs (rawEntries entries) query [] []) coeff.reverse

def replaceDone (regs : Fin 5 → Bool) (output : List Bool) : ReplaceData :=
  keepCoefficient (eraseData regs [] [] output []) []

abbrev replaceTail : Cmd 5 8 := .call
  (ProgramLinking.liftProgram prependRecordProgram replaceRegPorts replaceStackPorts)

abbrev dictionaryReplace : Cmd 5 8 := .seq
  (.call (ProgramLinking.liftProgram eraseScanProgram id Fin.castSucc)) replaceTail

theorem replaceTail_eval (regs : Fin 5 → Bool) (query coeff output : List Bool) :
    ∃ final, Eval replaceTail (4 * query.length + 4 * coeff.length + 13)
      (keepCoefficient (eraseData regs [] query output []) coeff.reverse)
      (replaceDone final (Encoding.frame query ++ Encoding.frame coeff ++ output)) := by
  let d := keepCoefficient (eraseData regs [] query output []) coeff.reverse
  obtain ⟨rr,ht⟩ := prependRecord_trace (regs ∘ replaceRegPorts) query coeff output
  let b := prependData rr [] [] (Encoding.frame query ++ Encoding.frame coeff ++ output)
  let final := (embedState replaceRegPorts replaceStackPorts d b).regs
  have ha : embedState replaceRegPorts replaceStackPorts d
      (prependData (regs ∘ replaceRegPorts) query.reverse coeff.reverse output) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ replaceRegPorts_injective replaceStackPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [d,keepCoefficient,eraseData,extendStorage,SubexponentialSAT.SubexpRecordScan.storage,replaceStackPorts,prependData]
    · intros; rfl
  have hb : embedState replaceRegPorts replaceStackPorts d b =
      replaceDone final (Encoding.frame query ++ Encoding.frame coeff ++ output) := by
    apply embedState_eq_of_ports _ _ _ _ _ replaceRegPorts_injective replaceStackPorts_injective
    · intro i
      exact embedState_register replaceRegPorts replaceStackPorts d b replaceRegPorts_injective i
    · intro i hi
      exact embedState_register_frame replaceRegPorts replaceStackPorts d b i hi
    · intro i; fin_cases i <;> simp [b,replaceDone,keepCoefficient,eraseData,extendStorage,SubexponentialSAT.SubexpRecordScan.storage,replaceStackPorts,prependData]
    · intro i hi
      fin_cases i <;> simp_all [d,replaceDone,keepCoefficient,eraseData,extendStorage,SubexponentialSAT.SubexpRecordScan.storage,replaceStackPorts,Fin.exists_fin_succ]
  have he := eval_call_lifted prependRecordProgram replaceRegPorts replaceStackPorts d
    replaceRegPorts_injective replaceStackPorts_injective ht
  change Eval replaceTail _
    (embedState replaceRegPorts replaceStackPorts d (prependData (regs ∘ replaceRegPorts) query.reverse coeff.reverse output))
    (embedState replaceRegPorts replaceStackPorts d b) at he
  rw [ha,hb] at he
  exact ⟨final,he⟩

theorem dictionaryReplace_eval (entries : List ByteRecord) (query coeff : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 4 * query.length + 4 * coeff.length + 16, ∃ final,
      Eval dictionaryReplace n (replaceData regs entries query coeff)
        (replaceDone final (rawEntries ((query,coeff)::(erasedEntries query entries).reverse))) := by
  obtain ⟨n,hn,middle,he⟩ := eraseScan_trace entries query [] regs
  have hcall := eval_call_lifted eraseScanProgram id Fin.castSucc
    (replaceData regs entries query coeff) Function.injective_id (Fin.castSucc_injective 7) he
  change Eval _ n
    (embedState id Fin.castSucc (keepCoefficient (eraseData regs (rawEntries entries) query [] []) coeff.reverse)
      (eraseData regs (rawEntries entries) query [] []))
    (embedState id Fin.castSucc (keepCoefficient (eraseData regs (rawEntries entries) query [] []) coeff.reverse)
      (eraseData middle [] query (rawEntries (erasedEntries query entries).reverse ++ []) [])) at hcall
  simp only [embedSeven,List.append_nil] at hcall
  obtain ⟨final,ht⟩ := replaceTail_eval middle query coeff (rawEntries (erasedEntries query entries).reverse)
  refine ⟨n+(4*query.length+4*coeff.length+13),by omega,final,?_⟩
  exact hcall.seq ht

def dictionaryReplaceProgram := compiled dictionaryReplace 0 5

theorem dictionaryReplace_trace (entries : List ByteRecord) (query coeff : List Bool) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget query entries + 4 * query.length + 4 * coeff.length + 17, ∃ final,
      Trace dictionaryReplaceProgram n
        ((replaceData regs entries query coeff).withPC (some dictionaryReplaceProgram.entry))
        ((replaceDone final (rawEntries ((query,coeff)::(erasedEntries query entries).reverse))).withPC none) := by
  obtain ⟨n,hn,final,he⟩ := dictionaryReplace_eval entries query coeff regs
  exact ⟨n+1,by omega,final,compiled_halt_trace he 0 5⟩
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
