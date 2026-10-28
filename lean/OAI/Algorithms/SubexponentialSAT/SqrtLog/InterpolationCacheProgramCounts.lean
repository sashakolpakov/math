import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount

namespace OAI.Algorithms

/-! Paid materialization of canonical unary word and table lengths. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def countRegisters (i : Fin 3) : Fin 16 := i.castAdd 13

def countPorts (src dst : Fin 320) : Fin 2 → Fin 320 := ![src,dst]

def consumeCount (src dst : Fin 320) : Code :=
  .call (ProgramLinking.liftProgram PackingHeadProgramPrepareCount.program countRegisters (countPorts src dst))

theorem consumeCount_run (src dst : Fin 320) (hne : src≠dst) (s : Store) :
    Runs (consumeCount src dst) (4*(s src).length+4) s
      (Function.update (Function.update s src []) dst (List.replicate (s src).length true++s dst)) := by
  intro r
  have hr : Function.Injective countRegisters := Fin.castAdd_injective _ _
  have hp : Function.Injective (countPorts src dst) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [countPorts]
  let a : Data := ⟨r,s⟩
  let out := Function.update (Function.update s src []) dst (List.replicate (s src).length true++s dst)
  let b := PackingHeadProgramPrepareCount.state (fun _ => false) [] (List.replicate (s src).length true++s dst)
  have ht := PackingHeadProgramPrepareCount.trace (r ∘ countRegisters) (s src) (s dst)
  have hproject : projectState countRegisters (countPorts src dst) a =
      PackingHeadProgramPrepareCount.state (r ∘ countRegisters) (s src) (s dst) := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> rfl
  have he := eval_call_from_state PackingHeadProgramPrepareCount.program countRegisters
    (countPorts src dst) a hr hp (by rw [hproject]; exact ht)
  have hb : embedState countRegisters (countPorts src dst) a b=
      (⟨(embedState countRegisters (countPorts src dst) a b).regs,out⟩ : Data) := by
    apply embedState_eq_of_ports countRegisters (countPorts src dst) a _ b hr hp
    · intro i; exact embedState_register countRegisters (countPorts src dst) a b hr i
    · intro i hi; exact embedState_register_frame countRegisters (countPorts src dst) a b i hi
    · intro i; fin_cases i <;> simp [out,b,PackingHeadProgramPrepareCount.state,countPorts,hne]
    · intro i hi
      have hs : i≠src := by intro h; apply hi; exact ⟨0,by simpa [countPorts] using h.symm⟩
      have hd : i≠dst := by intro h; apply hi; exact ⟨1,by simpa [countPorts] using h.symm⟩
      change out i=s i
      simp [out,hs,hd]
  change Eval (consumeCount src dst) (4*(s src).length+4) a
    (embedState countRegisters (countPorts src dst) a b) at he
  rw [hb] at he
  exact ⟨_,_,le_rfl,he⟩

def countCopy (src dst : Fin 320) : Code := .seq (copy src 272) (consumeCount 272 dst)

theorem countCopy_run (src dst : Fin 320) (s : Store)
    (hs : src≠272) (hs270 : src≠270) (hd : dst≠272)
    (ht : s 270=[]) (hw : s 272=[]) (ho : s dst=[]) :
    Runs (countCopy src dst) (11*(s src).length+9) s
      (Function.update s dst (List.replicate (s src).length true)) := by
  let mid := Function.update s 272 (s src)
  have h1 : Runs (copy src 272) (7*(s src).length+5) s mid := by
    simpa only [mid,hw,List.append_nil] using copy_run s src 272 hs hs270 (by decide) ht
  have h2 := consumeCount_run 272 dst hd.symm mid
  have he : Function.update (Function.update mid 272 []) dst
      (List.replicate (mid 272).length true++mid dst) =
      Function.update s dst (List.replicate (s src).length true) := by
    simp only [mid,Function.update_same,Function.update_idem,Function.update_of_ne hd,ho,List.append_nil]
    rw [← hw,Function.update_eq_self]
  rw [he] at h2
  have h := h1.seq h2
  exact h.mono (by simp [mid]; omega)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
