import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage

namespace OAI.Algorithms

/-! Save the selector's caller registers on a temporary prefix of an outer
stack. Its arbitrary original tail is restored, so no empty outer bank is
assumed. The native query only touches worker stacks below 768. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls

abbrev FrameData := State 40 896

def pushedRegister (i : Fin 40) (a : FrameData) : FrameData :=
  ⟨a.regs,Function.update a.stacks 895 (a.regs i::a.stacks 895)⟩
def poppedRegister (i : Fin 40) (a : FrameData) : FrameData :=
  ⟨readRegs a.regs i 0 (a.stacks 895).head?,Function.update a.stacks 895 (a.stacks 895).tail⟩

def saveRegisters : List (Fin 40) → Cmd 40 896
  | [] => .base .skip
  | i::is => .seq (.base (.atom (.push 895 i))) (saveRegisters is)
def savedRegisters : List (Fin 40) → FrameData → FrameData
  | [],a => a
  | i::is,a => savedRegisters is (pushedRegister i a)
def restoreRegisters : List (Fin 40) → Cmd 40 896
  | [] => .base .skip
  | i::is => .seq (.base (.atom (.pop 895 i 0))) (restoreRegisters is)
def restoredRegisters : List (Fin 40) → FrameData → FrameData
  | [],a => a
  | i::is,a => restoredRegisters is (poppedRegister i a)

theorem saveRegisters_eval (is : List (Fin 40)) (a : FrameData) :
    Eval (saveRegisters is) is.length a (savedRegisters is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip a)
  | cons i is ih =>
    have hp : Eval (.base (.atom (.push 895 i))) 1 a (pushedRegister i a) := .base (.atom _ _)
    simpa only [saveRegisters,savedRegisters,List.length_cons,Nat.add_comm] using hp.seq (ih _)

theorem restoreRegisters_eval (is : List (Fin 40)) (a : FrameData) :
    Eval (restoreRegisters is) is.length a (restoredRegisters is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip a)
  | cons i is ih =>
    have hp : Eval (.base (.atom (.pop 895 i 0))) 1 a (poppedRegister i a) := .base (.atom _ _)
    simpa only [restoreRegisters,restoredRegisters,List.length_cons,Nat.add_comm] using hp.seq (ih _)

theorem savedRegisters_eq (is : List (Fin 40)) (a : FrameData) :
    savedRegisters is a =
      ⟨a.regs,Function.update a.stacks 895 ((is.map a.regs).reverse++a.stacks 895)⟩ := by
  induction is generalizing a with
  | nil => simp [savedRegisters]
  | cons i is ih =>
    rw [savedRegisters,ih]
    simp [pushedRegister,List.reverse_cons,List.append_assoc]

def replayRegisters : List (Fin 40) → (Fin 40 → Bool) → (Fin 40 → Bool) → (Fin 40 → Bool)
  | [],_,current => current
  | i::is,original,current => replayRegisters is original (readRegs current i 0 (some (original i)))

theorem restoredRegisters_eq (is : List (Fin 40)) (original : Fin 40 → Bool)
    (a : FrameData) (tail : List Bool) (hs : a.stacks 895=is.map original++tail) :
    restoredRegisters is a =
      ⟨replayRegisters is original a.regs,Function.update a.stacks 895 tail⟩ := by
  induction is generalizing a with
  | nil =>
    simp only [List.map_nil,List.nil_append] at hs
    simp [restoredRegisters,replayRegisters,←hs]
  | cons i is ih =>
    rw [restoredRegisters,ih (poppedRegister i a)]
    · simp [poppedRegister,replayRegisters,hs]
    · simp [poppedRegister,hs]

theorem replayRegisters_value (is : List (Fin 40)) (original current : Fin 40 → Bool)
    (i : Fin 40) (hi : i≠0) :
    replayRegisters is original current i = if i∈is then original i else current i := by
  induction is generalizing current with
  | nil => simp [replayRegisters]
  | cons j is ih =>
    rw [replayRegisters,ih]
    by_cases ht : i∈is
    · simp [ht]
    · by_cases he : i=j
      · subst j; simp [ht,readRegs,hi]
      · simp [ht,he,readRegs,hi]

def callerRegisters : List (Fin 40) :=
  (List.finRange 32).map fun i => ⟨i.val+8,by omega⟩
abbrev saveCaller : Cmd 40 896 := saveRegisters callerRegisters
abbrev restoreCaller : Cmd 40 896 := restoreRegisters callerRegisters.reverse

theorem callerRegisters_length : callerRegisters.length=32 := by simp [callerRegisters]
theorem mem_callerRegisters (i : Fin 40) : i ∈ callerRegisters ↔ (8 : ℕ) ≤ i.val := by
  constructor
  · intro hi
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hi
    have h := congrArg Fin.val hj
    simp only at h
    omega
  · intro hi
    apply List.mem_map.mpr
    refine ⟨⟨i.val-8,by have := i.isLt; omega⟩,by simp,?_⟩
    apply Fin.ext
    simp only
    omega

abbrev protectCaller (body : Cmd 40 896) : Cmd 40 896 :=
  .seq saveCaller (.seq body restoreCaller)

theorem protectCaller_eval (body : Cmd 40 896) (a b : FrameData) (n : ℕ)
    (he : Eval body n (savedRegisters callerRegisters a) b)
    (hs : b.stacks 895=(savedRegisters callerRegisters a).stacks 895) :
    ∃ c, Eval (protectCaller body) (n+64) a c ∧
      (∀ i : Fin 40, (8 : ℕ) ≤ i.val → c.regs i=a.regs i) ∧
      c.stacks 895=a.stacks 895 ∧
      (∀ i : Fin 896,i≠895 → c.stacks i=b.stacks i) := by
  let c := restoredRegisters callerRegisters.reverse b
  have hrestore := restoreRegisters_eval callerRegisters.reverse b
  have hsave := saveRegisters_eval callerRegisters a
  have hbits : b.stacks 895=callerRegisters.reverse.map a.regs++a.stacks 895 := by
    rw [hs,savedRegisters_eq]
    simp only [Function.update_same,List.map_reverse]
  have hc := restoredRegisters_eq callerRegisters.reverse a.regs b (a.stacks 895) hbits
  refine ⟨c,?_,?_,?_,?_⟩
  · have h := hsave.seq (he.seq hrestore)
    simpa only [protectCaller,saveCaller,restoreCaller,List.length_reverse,
      callerRegisters_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  · intro i hi
    change (restoredRegisters callerRegisters.reverse b).regs i=a.regs i
    rw [hc]
    exact (replayRegisters_value _ _ _ i (by intro h; subst i; simp at hi)).trans
      (ite_eq_left (by simpa using (mem_callerRegisters i).mpr hi))
  · change (restoredRegisters callerRegisters.reverse b).stacks 895=a.stacks 895
    simp only [hc,Function.update_same]
  · intro i hi
    change (restoredRegisters callerRegisters.reverse b).stacks i=b.stacks i
    simp only [hc,Function.update_of_ne hi]

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
