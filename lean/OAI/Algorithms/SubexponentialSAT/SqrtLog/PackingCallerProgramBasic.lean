import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputEndpoint
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost

namespace OAI.Algorithms

/-! Framed local storage for the concrete packing caller. Ports53/54 retain
width/alphabet,55..59 parameters,60 scopes,61 plans,62 words,63 metadata. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram
abbrev Small := State 16 48
abbrev Local := State 16 64
abbrev Code := Cmd 16 64
abbrev Store := Fin 64 → List Bool

def setRegs (d : Small) (regs : Fin 16 → Bool) : Small := ⟨regs,d.stacks⟩

private theorem high_not_low (j : Fin 64) (hj : 48 ≤ j.val) :
    ¬ ∃ i, lowPorts i=j := by
  rintro ⟨i,h⟩
  have hv := congrArg Fin.val h
  change i.val=j.val at hv
  have := i.isLt
  omega

theorem framed_update_high (outside : Store) (d : Small) (j : Fin 64)
    (hj : 48 ≤ j.val) (bits : List Bool) :
    (framed (Function.update outside j bits) d).stacks =
      Function.update (framed outside d).stacks j bits := by
  funext i
  by_cases hij : i=j
  · subst i
    simp [framed_outside _ _ j (high_not_low j hj)]
  · rw [Function.update_of_ne hij]
    by_cases hi : i.val < 48
    · simp [framed_stack,hi]
    · simp [framed_stack,hi,hij]

def saveHigh (src : Fin 48) (dst : Fin 64) : Code := copyCmd (lowPorts src) dst 52

/-- A paid low-to-high copy retains the entire low state and all other masters. -/
theorem saveHigh_eval (outside : Store) (d : Small) (src : Fin 48) (dst : Fin 64)
    (hd : 48 ≤ dst.val) (h52 : (52 : Fin 64)≠dst)
    (ht : outside 52=[]) (hz : outside dst=[]) :
    ∃ rf, Eval (saveHigh src dst) (7*(d.stacks src).length+5)
      (framed outside d)
      (framed (Function.update outside dst (d.stacks src)) (setRegs d rf)) := by
  have hsd : lowPorts src≠dst := by
    intro h; exact high_not_low dst hd ⟨src,h⟩
  have hst : lowPorts src≠(52 : Fin 64) := by
    intro h; exact high_not_low 52 (by decide) ⟨src,h⟩
  have htmp : (framed outside d).stacks 52=[] := by
    rw [framed_outside _ _ 52 (high_not_low 52 (by decide)),ht]
  have hdst : (framed outside d).stacks dst=[] := by
    rw [framed_outside _ _ dst (high_not_low dst hd),hz]
  have h := copy_eval (lowPorts src) dst 52 (framed outside d) hsd hst h52 htmp
  let e := copyState (lowPorts src) dst (framed outside d)
  have he : e=framed (Function.update outside dst (d.stacks src)) (setRegs d e.regs) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [setRegs]
    · rw [framed_update_high _ _ _ hd]
      funext i
      simp only [e,copyState_stack,framed_low,hdst,List.append_nil]
      congr 1
  simp only [framed_low] at h
  change Eval (saveHigh src dst) _ _ e at h
  rw [he] at h
  exact ⟨e.regs,h⟩

def lowClearPorts : List (Fin 64) := (List.finRange 48).map lowPorts
def clearLow : Code := clearMany lowClearPorts

@[simp] theorem mem_lowClearPorts (i : Fin 64) : i∈lowClearPorts ↔ i.val < 48 := by
  simp only [lowClearPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega
  · intro hi
    exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩

theorem clearLow_eval (outside : Store) (d : Small) :
    ∃ rf, Eval clearLow (clearManyCost lowClearPorts (framed outside d))
      (framed outside d) (framed outside (⟨rf,fun _=>[]⟩ : Small)) := by
  let e := clearManyState lowClearPorts (framed outside d)
  have he : e=framed outside (⟨e.regs,fun _=>[]⟩ : Small) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp
    · funext i
      simp only [e,clearMany_stacks,mem_lowClearPorts,framed_stack]
      split <;> simp_all
  have h := clearMany_eval lowClearPorts (framed outside d)
  change Eval clearLow _ _ e at h
  rw [he] at h
  exact ⟨e.regs,h⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
