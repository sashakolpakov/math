import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyControl

namespace OAI.Algorithms

/-! Frame an actual completed incidence dictionary under its original variable
ID. The table accumulator is229; all coefficient-emitter work ports are free. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open SubexpPolynomialConstructor

def tableMap : Equiv.Perm (Fin 256) := Equiv.swap 217 229

def emitTable : Code :=
  liftCommand PerturbationEmitProgram.emitCommand 0 0 id tableMap

theorem emitTable_run (s : Store) (key payload : List Bool)
    (hk : s 222=key.reverse) (hp : s 228=payload.reverse) :
    ExecutesIn emitTable (4*key.length+4*payload.length+14) s
      (Function.update (Function.update (Function.update s 222 []) 228 [])
        229 (Encoding.frame key++Encoding.frame payload++s 229)) := by
  intro regs
  have h := PerturbationEmitProgram.emit_run (s ∘ tableMap) key payload
    (by
      change s (tableMap 222) = key.reverse
      rw [show tableMap 222 = 222 by decide]
      exact hk)
    (by
      change s (tableMap 228) = payload.reverse
      rw [show tableMap 228 = 228 by decide]
      exact hp)
  obtain ⟨n,rf,hn,he⟩ := h regs
  have hl := eval_liftCommand_from_state PerturbationEmitProgram.emitCommand
    0 0 id tableMap (⟨regs,s⟩ : Data) Function.injective_id tableMap.injective he
  let out := Function.update (Function.update (Function.update s 222 []) 228 [])
    229 (Encoding.frame key++Encoding.frame payload++s 229)
  have hext : Function.extend tableMap (s ∘ tableMap) s=s := by
    exact congrArg StructuredProgram.State.stacks
      (embedState_project id tableMap (⟨regs,s⟩ : Data) Function.injective_id tableMap.injective)
  have hout : embedState id tableMap (⟨regs,s⟩ : Data)
      (⟨rf,Function.update (Function.update (Function.update (s ∘ tableMap) 222 []) 228 [])
        217 (Encoding.frame key++Encoding.frame payload++(s ∘ tableMap) 217)⟩ : Data) =
      (⟨rf,out⟩ : Data) := by
    apply state_ext
    · simp [embedState]
    · change Function.extend tableMap _ s=out
      rw [ProgramLinking.extend_update tableMap.injective,
        ProgramLinking.extend_update tableMap.injective,
        ProgramLinking.extend_update tableMap.injective,hext]
      have h222 : tableMap 222=222 := by decide
      have h228 : tableMap 228=228 := by decide
      have h217 : tableMap 217=229 := by decide
      simp only [h222,h228,h217,Function.comp_apply]
      rfl
  change Eval emitTable (n+1) (⟨regs,s⟩ : Data) _ at hl
  rw [hout] at hl
  exact ⟨n+1,rf,by omega,hl⟩

def prepareEntry : Code := .seq (copy 215 222)
  (.seq (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1))
    (.seq (move 217 228)
      (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))))

def entry : Code := .seq prepareEntry emitTable

def entryScratch : List (Fin 256) := [120,222,223,224,226,227,228,245]

theorem entry_run (s : Store) (he : ∀ i ∈ entryScratch, s i=[]) :
    ExecutesIn entry (20*(s 215).length+19*(s 217).length+39) s
      (Function.update (Function.update s 217 []) 229
        (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229)) := by
  let s1 := Function.update s 222 (s 215)
  let s2 := Function.update s 222 (s 215).reverse
  let s3 := Function.update (Function.update s2 217 []) 228 (s 217)
  let s4 := Function.update (Function.update s2 217 []) 228 (s 217).reverse
  have h1 : ExecutesIn (copy 215 222) (7*(s 215).length+5) s s1 := by
    simpa [s1,he 222 (by simp [entryScratch])] using
      copy_run 215 222 s (by decide) (by decide) (by decide)
        (he 120 (by simp [entryScratch]))
  have h2 : ExecutesIn (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1))
      (9*(s 215).length+7) s1 s2 := by
    intro regs
    have h := reverse_eval (⟨regs,s1⟩ : Data) 222 223 224 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [s1] using he 223 (by simp [entryScratch]))
      (by simpa [s1] using he 224 (by simp [entryScratch]))
    exact ⟨9*(s 215).length+7,_,le_rfl,by simpa [s1,s2,afterReverse,StackRoutines.reverseStacks] using h⟩
  have h3 : ExecutesIn (move 217 228) (6*(s 217).length+6) s2 s3 := by
    simpa [s3,s2] using move_run s2 217 228 (by decide) (by decide) (by decide)
      (by simpa [s2] using he 245 (by simp [entryScratch]))
      (by simpa [s2] using he 228 (by simp [entryScratch]))
  have h4 : ExecutesIn (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))
      (9*(s 217).length+7) s3 s4 := by
    intro regs
    have h := reverse_eval (⟨regs,s3⟩ : Data) 228 226 227 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [s3,s2] using he 226 (by simp [entryScratch]))
      (by simpa [s3,s2] using he 227 (by simp [entryScratch]))
    exact ⟨9*(s 217).length+7,_,le_rfl,by simpa [s4,s3,afterReverse,StackRoutines.reverseStacks] using h⟩
  have hout : Function.update (Function.update (Function.update s4 222 []) 228 [])
      229 (Encoding.frame (s 215)++Encoding.frame (s 217)++s4 229) =
      Function.update (Function.update s 217 []) 229
        (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229) := by
    funext i
    by_cases h217 : i=217 <;> by_cases h222 : i=222 <;>
      by_cases h228 : i=228 <;> by_cases h229 : i=229 <;>
      simp [s4,s2,h217,h222,h228,h229,
        he 222 (by simp [entryScratch]),he 228 (by simp [entryScratch])]
  have h5 := emitTable_run s4 (s 215) (s 217)
    (by simp [s4,s2]) (by simp [s4])
  rw [hout] at h5
  have h := (h1.seq (h2.seq (h3.seq h4))).seq h5
  convert h using 1 <;> first | rfl | ring

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
