import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Physical construction of a type-bit offset from unary metadata. -/

namespace SubexponentialSAT.Subexp.TypeIndexProgram

open BitProgram StructuredCalls TupleProgram

abbrev Data := State 8 16
abbrev unary (n : ℕ) := List.replicate n true

def repeatRegisters : Fin 3 → Fin 8 := ![3,4,5]
def repeatStacks (src : Fin 16) : Fin 4 → Fin 16 := ![src,1,5,7]
theorem repeatRegisters_injective : Function.Injective repeatRegisters := by decide
theorem repeatStacks_injective (src : Fin 16) (h1 : src ≠ 1) (h5 : src ≠ 5) (h7 : src ≠ 7) :
    Function.Injective (repeatStacks src) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [repeatStacks]

abbrev reset : Cmd 8 16 := .base (CandidateScoreProgram.resetList [3,4,5])
def resetState (a : Data) : Data :=
  ⟨CandidateScoreProgram.resetValues [3,4,5] a.regs,a.stacks⟩

theorem reset_eval (a : Data) : Eval reset 3 a (resetState a) :=
  .base (CandidateScoreProgram.resetList_eval [3,4,5] a)

def repeated (src : Fin 16) (n : ℕ) (a : Data) : Data :=
  ⟨(resetState a).regs,
    Function.update (Function.update a.stacks 1 (BlockCopyProgram.copies n (a.stacks src) ++ a.stacks 1)) 7 []⟩

abbrev repeatAdd (src : Fin 16) : Cmd 8 16 :=
  .seq reset (.call (ProgramLinking.liftProgram BlockCopyProgram.program repeatRegisters (repeatStacks src)))

theorem repeatAdd_eval (src : Fin 16) (h1 : src ≠ 1) (h5 : src ≠ 5) (h7 : src ≠ 7)
    (a : Data) (n : ℕ) (hc : a.stacks 7 = unary n) (ht : a.stacks 5 = []) :
    Eval (repeatAdd src) (n * (7 * (a.stacks src).length + 7) + 6) a (repeated src n a) := by
  let b := resetState a
  have hs := repeatStacks_injective src h1 h5 h7
  have hi : embedState repeatRegisters (repeatStacks src) b
      (BlockCopyProgram.initialState n (a.stacks src) (a.stacks 1)) = b := by
    apply SubexpScanPrimitives.embedState_eq _ _ repeatRegisters_injective hs
    · intro i; fin_cases i <;>
        simp [b,resetState,repeatRegisters,CandidateScoreProgram.resetValues_apply,
          BlockCopyProgram.initialState,BlockCopyProgram.data]
    · intro i; fin_cases i <;>
        simp [b,resetState,repeatStacks,BlockCopyProgram.initialState,BlockCopyProgram.data,hc,ht]
    · intros; rfl
    · intros; rfl
  have ho : embedState repeatRegisters (repeatStacks src) b
      (BlockCopyProgram.data false false (a.stacks src)
        (BlockCopyProgram.copies n (a.stacks src) ++ a.stacks 1) []) = repeated src n a := by
    apply SubexpScanPrimitives.embedState_eq _ _ repeatRegisters_injective hs
    · intro i; fin_cases i <;>
        simp [repeated,resetState,repeatRegisters,CandidateScoreProgram.resetValues_apply,
          BlockCopyProgram.data]
    · intro i; fin_cases i <;>
        simp [repeated,repeatStacks,BlockCopyProgram.data,h1,h7,ht]
    · intro i _; rfl
    · intro i hi
      have hi1 : i ≠ 1 := fun h => hi ⟨1,by simpa [repeatStacks] using h.symm⟩
      have hi7 : i ≠ 7 := fun h => hi ⟨3,by simpa [repeatStacks] using h.symm⟩
      simp [repeated,b,resetState,hi1,hi7]
  have hh := eval_call_lifted BlockCopyProgram.program repeatRegisters (repeatStacks src) b
    repeatRegisters_injective hs (BlockCopyProgram.program_trace n (a.stacks src) (a.stacks 1))
  rw [hi,ho] at hh
  convert (reset_eval a).seq hh using 1 ; omega

theorem copies_unary (n m : ℕ) : BlockCopyProgram.copies n (unary m) = unary (n * m) := by
  induction n with
  | zero => simp only [BlockCopyProgram.copies_zero,Nat.zero_mul,unary,List.replicate_zero]
  | succ n ih =>
      rw [BlockCopyProgram.copies_succ,ih]
      change List.replicate (n * m) true ++ List.replicate m true = List.replicate ((n + 1) * m) true
      rw [← List.replicate_add,Nat.add_mul,Nat.one_mul]

def copied (src dst : Fin 16) (a : Data) : Data :=
  ⟨readRegs a.regs 3 4 none,StackRoutines.copyStacks src dst a.stacks⟩

abbrev headCommand : Cmd 8 16 :=
  .seq (.call (StackRoutines.copyProgram 13 1 5 3 4))
    (.seq (.call (StackRoutines.copyProgram 12 7 5 3 4)) (repeatAdd 11))

def headResult (_r t _g : ℕ) (a : Data) : Data :=
  repeated 11 t (copied 12 7 (copied 13 1 a))

def headCost (r t g : ℕ) : ℕ := 7 * g + 7 * t + t * (7 * r + 7) + 16

theorem head_eval (r t g : ℕ) (a : Data)
    (hr : a.stacks 11 = unary r) (ht : a.stacks 12 = unary t) (hg : a.stacks 13 = unary g)
    (_h1 : a.stacks 1 = []) (h5 : a.stacks 5 = []) (h7 : a.stacks 7 = []) :
    Eval headCommand (headCost r t g) a (headResult r t g a) := by
  let b := copied 13 1 a
  let c := copied 12 7 b
  have hcopy1 := copy_eval 13 1 5 3 4 (by decide) (by decide) (by decide) (by decide) a h5
  have hcopy2 := copy_eval 12 7 5 3 4 (by decide) (by decide) (by decide) (by decide) b
    (by simp [b,copied,StackRoutines.copyStacks,h5])
  have hrep := repeatAdd_eval 11 (by decide) (by decide) (by decide) c t
    (by simp [c,b,copied,StackRoutines.copyStacks,h7,ht])
    (by simp [c,b,copied,StackRoutines.copyStacks,h5])
  have h := hcopy1.seq (hcopy2.seq hrep)
  have hb12 : b.stacks 12 = unary t := by simp [b,copied,StackRoutines.copyStacks,ht]
  have hc11 : c.stacks 11 = unary r := by simp [c,b,copied,StackRoutines.copyStacks,hr]
  change Eval headCommand
    ((7 * (a.stacks 13).length + 5) + ((7 * (b.stacks 12).length + 5) +
      (t * (7 * (c.stacks 11).length + 7) + 6))) a (headResult r t g a) at h
  rw [hg,hb12,hc11] at h
  simp only [unary,List.length_replicate] at h
  convert h using 1 ; simp only [headCost] ; omega

theorem headResult_output (r t g : ℕ) (a : Data) (hr : a.stacks 11 = unary r)
    (hg : a.stacks 13 = unary g) (h1 : a.stacks 1 = []) :
    (headResult r t g a).stacks 1 = unary (t * r + g) := by
  let b := copied 12 7 (copied 13 1 a)
  have hb11 : b.stacks 11 = unary r := by simp [b,copied,StackRoutines.copyStacks,hr]
  have hb1 : b.stacks 1 = unary g := by simp [b,copied,StackRoutines.copyStacks,hg,h1]
  change BlockCopyProgram.copies t (b.stacks 11) ++ b.stacks 1 = unary (t * r + g)
  rw [hb11,hb1,copies_unary]
  exact (List.replicate_add (t * r) g true).symm

theorem headResult_frame (r t g : ℕ) (a : Data) (j : Fin 16) (h1 : j ≠ 1) (h7 : j ≠ 7) :
    (headResult r t g a).stacks j = a.stacks j := by
  simp [headResult,repeated,copied,StackRoutines.copyStacks,h1,h7]

@[simp] theorem headResult_count (r t g : ℕ) (a : Data) : (headResult r t g a).stacks 7 = [] := by
  simp [headResult,repeated]

abbrev jointCommand : Cmd 8 16 :=
  .seq headCommand (.seq (.call (StackRoutines.copyProgram 15 7 5 3 4))
    (.seq (pushConst 7 3 true) (repeatAdd 14)))

def jointResult (r t g i : ℕ) (a : Data) : Data :=
  repeated 14 (i + 1) (pushedState 7 3 true (copied 15 7 (headResult r t g a)))

def jointCost (r width t g i : ℕ) : ℕ :=
  headCost r t g + (7 * i + 5 + (2 + ((i + 1) * (7 * width + 7) + 6)))

theorem joint_eval (r width t g i : ℕ) (a : Data)
    (hr : a.stacks 11 = unary r) (ht : a.stacks 12 = unary t) (hg : a.stacks 13 = unary g)
    (hw : a.stacks 14 = unary width) (hi : a.stacks 15 = unary i)
    (h1 : a.stacks 1 = []) (h5 : a.stacks 5 = []) (h7 : a.stacks 7 = []) :
    Eval jointCommand (jointCost r width t g i) a (jointResult r t g i a) := by
  let b := headResult r t g a
  let c := copied 15 7 b
  let d := pushedState 7 3 true c
  have hb5 : b.stacks 5 = [] := (headResult_frame r t g a 5 (by decide) (by decide)).trans h5
  have hb15 : b.stacks 15 = unary i :=
    (headResult_frame r t g a 15 (by decide) (by decide)).trans hi
  have hb14 : b.stacks 14 = unary width :=
    (headResult_frame r t g a 14 (by decide) (by decide)).trans hw
  have h2 := copy_eval 15 7 5 3 4 (by decide) (by decide) (by decide) (by decide) b hb5
  have h3 := pushConst_eval 7 3 true c
  have h4 := repeatAdd_eval 14 (by decide) (by decide) (by decide) d (i + 1)
    (by simp [d,c,copied,StackRoutines.copyStacks,b,hb15,unary,List.replicate_succ])
    (by simp [d,c,copied,StackRoutines.copyStacks,hb5])
  have h := (head_eval r t g a hr ht hg h1 h5 h7).seq (h2.seq (h3.seq h4))
  have hd14 : d.stacks 14 = unary width := by
    simp [d,c,copied,StackRoutines.copyStacks,hb14]
  change Eval jointCommand (headCost r t g + ((7 * (b.stacks 15).length + 5) +
    (2 + ((i + 1) * (7 * (d.stacks 14).length + 7) + 6)))) a (jointResult r t g i a) at h
  rw [hb15,hd14] at h
  simp only [unary,List.length_replicate] at h
  exact h

theorem jointResult_output (r width t g i : ℕ) (a : Data)
    (hr : a.stacks 11 = unary r) (hg : a.stacks 13 = unary g)
    (hw : a.stacks 14 = unary width) (h1 : a.stacks 1 = []) :
    (jointResult r t g i a).stacks 1 = unary ((i + 1) * width + (t * r + g)) := by
  let b := pushedState 7 3 true (copied 15 7 (headResult r t g a))
  have hb14 : b.stacks 14 = unary width := by
    simp [b,copied,StackRoutines.copyStacks,
      headResult_frame r t g a 14 (by decide) (by decide),hw]
  have hb1 : b.stacks 1 = unary (t * r + g) := by
    simp [b,copied,StackRoutines.copyStacks,headResult_output r t g a hr hg h1]
  change BlockCopyProgram.copies (i + 1) (b.stacks 14) ++ b.stacks 1 = _
  rw [hb14,hb1,copies_unary]
  exact (List.replicate_add ((i + 1) * width) (t * r + g) true).symm

theorem jointResult_frame (r t g i : ℕ) (a : Data) (j : Fin 16) (h1 : j ≠ 1) (h7 : j ≠ 7) :
    (jointResult r t g i a).stacks j = a.stacks j := by
  simp [jointResult,repeated,pushedState,copied,StackRoutines.copyStacks,h1,h7,
    headResult_frame r t g a j h1 h7]

@[simp] theorem jointResult_count (r t g i : ℕ) (a : Data) : (jointResult r t g i a).stacks 7 = [] := by
  simp [jointResult,repeated]

end SubexponentialSAT.Subexp.TypeIndexProgram

end OAI.Algorithms
