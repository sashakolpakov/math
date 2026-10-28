import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheckRead
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

abbrev Store := Fin 340 → List Bool
abbrev Data := State 16 340
abbrev Code := Cmd 16 340

def ExecutesIn (c : Code) (K : ℕ) (s t : Store) : Prop :=
  ∀ regs, ∃ n rf, n ≤ K ∧ Eval c n (⟨regs,s⟩ : Data) (⟨rf,t⟩ : Data)

theorem ExecutesIn.seq {a b : Code} {A B : ℕ} {s t u : Store}
    (ha : ExecutesIn a A s t) (hb : ExecutesIn b B t u) :
    ExecutesIn (.seq a b) (A+B) s u := by
  intro regs
  obtain ⟨na,ra,hna,hea⟩ := ha regs
  obtain ⟨nb,rb,hnb,heb⟩ := hb ra
  exact ⟨na+nb,rb,by omega,hea.seq heb⟩

theorem ExecutesIn.mono {c : Code} {A B : ℕ} {s t : Store}
    (h : ExecutesIn c A s t) (hab : A ≤ B) : ExecutesIn c B s t := by
  intro regs
  obtain ⟨n,rf,hn,he⟩ := h regs
  exact ⟨n,rf,hn.trans hab,he⟩

def transfer (src dst : Fin 340) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def clear (src : Fin 340) : Code := .call (StackRoutines.clearProgram src 0 1)
def copy (src dst : Fin 340) : Code := .call (StackRoutines.copyProgram src dst 339 0 1)
def push (dst : Fin 340) (b : Bool) : Code := Subexp.TupleProgram.pushConst dst 0 b

theorem transfer_run (src dst : Fin 340) (s : Store) (h : src ≠ dst) :
    ExecutesIn (transfer src dst) (3*(s src).length+3) s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.transfer_eval (⟨regs,s⟩ : Data) src dst 0 1 h (by decide)
  exact ⟨_,_,le_rfl,he⟩

theorem copy_run (src dst : Fin 340) (s : Store) (hsd : src ≠ dst)
    (hst : src ≠ 339) (hdt : 339 ≠ dst) (ht : s 339=[]) :
    ExecutesIn (copy src dst) (7*(s src).length+5) s
      (Function.update s dst (s src++s dst)) := by
  intro regs
  have he := SubexpScanPrimitives.copy_eval (⟨regs,s⟩ : Data) src dst 339 0 1
    hsd hst hdt (by decide) ht
  refine ⟨_,readRegs regs 0 1 none,le_rfl,?_⟩
  simpa [copy,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using he

theorem clear_run (src : Fin 340) (s : Store) :
    ExecutesIn (clear src) (2*(s src).length+3) s (Function.update s src []) := by
  intro regs
  have ht := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 regs s) 2 rfl rfl
  refine ⟨_,readRegs regs 0 1 none,le_rfl,Eval.call _ ?_⟩
  simpa [StackRoutines.clearProgram,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,Nat.add_assoc] using ht

theorem push_run (dst : Fin 340) (b : Bool) (s : Store) :
    ExecutesIn (push dst b) 2 s (Function.update s dst (b::s dst)) := by
  intro regs
  exact ⟨2,Function.update regs 0 b,le_rfl,Subexp.TupleProgram.pushConst_eval dst 0 b ⟨regs,s⟩⟩

/-- 329 is the remaining fiber, 305 the current incidence column. -/
def readIndex : Code := .call (RowSelectionProgramTupleCheck.Read.program 329 305 0 1)

theorem readIndex_run (s : Store) (i : ℕ) (tail : List Bool)
    (hs : s 329=Encoding.encodeNat i++tail) (hc : s 305=[]) :
    ExecutesIn readIndex (3*i+3) s
      (Function.update (Function.update s 329 tail) 305 (List.replicate i true)) := by
  intro regs
  have h := RowSelectionProgramTupleCheck.Read.run (329 : Fin 340) 305 (0 : Fin 16) 1
    (by decide) (by decide) regs s i tail hs
  refine ⟨_,readRegs regs 0 1 (some false),le_rfl,Eval.call _ ?_⟩
  simpa [RowSelectionProgramTupleCheck.Read.start,RowSelectionProgramTupleCheck.Read.finish,
    StructuredProgram.State.withPC,hc] using h

/-- The reverse accumulator333 receives a genuine source followed by add. -/
def appendSource : Code := .seq (transfer 287 333) (.seq (push 333 true) (push 333 false))

def appendResult (s : Store) : Store :=
  Function.update (Function.update s 287 []) 333
    ((s 333).reverse++s 287++[true,false]).reverse

theorem appendSource_run (s : Store) :
    ExecutesIn appendSource (3*(s 287).length+7) s (appendResult s) := by
  let s1 := Function.update (Function.update s 287 []) 333 ((s 287).reverse++s 333)
  let s2 := Function.update s1 333 (true::s1 333)
  have h1 := transfer_run 287 333 s (by decide)
  have h2 := push_run 333 true s1
  have h3 := push_run 333 false s2
  have he : Function.update s2 333 (false::s2 333)=appendResult s := by
    funext i
    by_cases hi : i=333
    · subst i
      simp [s2,s1,appendResult,List.reverse_append,List.reverse_cons,List.append_assoc]
    · simp [s2,s1,appendResult,hi]
  rw [he] at h3
  exact (h1.seq (h2.seq h3)).mono (by omega)

def zeroSource : Code := .seq (push 333 false) (push 333 false)

theorem zeroSource_run (s : Store) (h : s 333=[]) :
    ExecutesIn zeroSource 4 s (Function.update s 333 [false,false]) := by
  have h1 := push_run 333 false s
  have h2 := push_run 333 false (Function.update s 333 (false::s 333))
  have he : Function.update (Function.update s 333 (false::s 333)) 333
      (false::(Function.update s 333 (false::s 333)) 333)=Function.update s 333 [false,false] := by
    simp [h]
  rw [he] at h2
  exact h1.seq h2

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
