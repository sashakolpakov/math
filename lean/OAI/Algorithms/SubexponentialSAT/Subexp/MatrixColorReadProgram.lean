import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayPrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-! A fixed program that consumes one color word from each of the four
matrix-input streams. The word width is supplied as a unary stack. -/

namespace SubexponentialSAT.Subexp.MatrixColorReadProgram

open BitProgram StructuredCalls StackRoutines ArrayPrograms

abbrev Data := State 8 23

abbrev copyWidth : Cmd 8 23 := .call (copyProgram 21 10 0 0 1)

abbrev copiedWidth (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks 21 10 a.stacks⟩

theorem copyWidth_eval (a : Data) (h0 : a.stacks 0 = []) :
    Eval copyWidth (7 * (a.stacks 21).length + 5) a (copiedWidth a) :=
  TupleProgram.copy_eval 21 10 0 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a h0

abbrev take (src : Fin 23) : Cmd 8 23 :=
  .call (countedTransferProgram 10 src 4 0 1)

abbrev taken (a : Data) (src : Fin 23) (segment rest : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none, countedTransferStacks 10 src 4 segment rest a.stacks⟩

theorem take_eval (a : Data) (src : Fin 23) (segment rest : List Bool)
    (h10 : (10 : Fin 23) ≠ src) (h4 : src ≠ 4)
    (hs : a.stacks src = segment ++ rest)
    (hlen : (a.stacks 10).length = segment.length) :
    Eval (take src) (4 * segment.length + 3) a (taken a src segment rest) := by
  have ht := countedTransferProgram_trace (10 : Fin 23) src 4 (0 : Fin 8) 1
    h10 (by decide) h4 (by decide) segment rest (a.stacks 10) a.regs a.stacks hs rfl hlen
  have hh := halt_after_trace _ ht 4 rfl rfl
  exact .call _ (by simpa [taken, countedTransferResult, StructuredProgram.State.withPC,
    countedTransferProgram, Nat.add_assoc] using hh)

abbrev restore (dst : Fin 23) : Cmd 8 23 := .call (transferProgram 4 dst 0 1)

abbrev restored (a : Data) (dst : Fin 23) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks 4 dst a.stacks⟩

theorem restore_eval (a : Data) (dst : Fin 23) (h4 : (4 : Fin 23) ≠ dst) :
    Eval (restore dst) (3 * (a.stacks 4).length + 3) a (restored a dst) := by
  have ht := transferProgram_trace (4 : Fin 23) dst (0 : Fin 8) 1 h4 (by decide)
    a.regs a.stacks
  have hh := halt_after_trace _ ht 3 rfl rfl
  exact .call _ (by simpa [restore, restored, transferResult, StructuredProgram.State.withPC,
    transferProgram, Nat.add_assoc] using hh)

abbrev pull (src dst : Fin 23) : Cmd 8 23 :=
  .seq copyWidth (.seq (take src) (restore dst))

abbrev pulled (a : Data) (src dst : Fin 23) (segment rest : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks src rest) dst segment⟩

theorem pull_eval (a : Data) (src dst : Fin 23) (segment rest : List Bool)
    (hsrc : src ≠ 4 ∧ src ≠ 10 ∧ src ≠ 21)
    (hdst : dst ≠ 4 ∧ dst ≠ 10 ∧ dst ≠ 21) (hsd : src ≠ dst)
    (h0 : a.stacks 0 = []) (h4 : a.stacks 4 = []) (h10 : a.stacks 10 = [])
    (hd : a.stacks dst = []) (hs : a.stacks src = segment ++ rest)
    (hlen : (a.stacks 21).length = segment.length) :
    Eval (pull src dst) (14 * segment.length + 11) a
      (pulled a src dst segment rest) := by
  have hc := copyWidth_eval a h0
  have ht := take_eval (copiedWidth a) src segment rest hsrc.2.1.symm hsrc.1
    (by simpa [copiedWidth, copyStacks, hsrc.2.1, hsrc.2.2] using hs)
    (by simpa [copiedWidth, copyStacks, h10] using hlen)
  have hr := restore_eval (taken (copiedWidth a) src segment rest) dst hdst.1.symm
  have hfinish : restored (taken (copiedWidth a) src segment rest) dst =
      pulled a src dst segment rest := by
    apply MatrixProgramSupport.data_ext
    · simp [ readRegs_reset]
    · funext j
      by_cases hjd : j = dst
      · subst j
        simp [ transferStacks,
          countedTransferStacks, copyStacks,
          hdst.1, hdst.2.1, hsd.symm, hd, h4]
      · by_cases hjs : j = src
        · subst j
          simp [ transferStacks,
            countedTransferStacks, copyStacks, hjd, hsrc.1 ]
        · by_cases hj4 : j = 4
          · subst j
            simp [ transferStacks,
              countedTransferStacks, copyStacks, hjd, hjs, h4]
          · by_cases hj10 : j = 10
            · subst j
              simp [ transferStacks,
                countedTransferStacks, copyStacks, hjd, hjs, h10]
            · simp [ transferStacks,
                countedTransferStacks, copyStacks, hjd, hjs, hj4, hj10]
  rw [hfinish] at hr
  have he := hc.seq (ht.seq hr)
  convert he using 1
  simp [ countedTransferStacks, copyStacks, h4, hlen]
  ring

def source (i : Fin 4) : Fin 23 := ⟨17 + i.val, by omega⟩
def target (i : Fin 4) : Fin 23 := ⟨13 + i.val, by omega⟩

abbrev pullFour : Cmd 8 23 :=
  .seq (pull 17 13) (.seq (pull 18 14) (.seq (pull 19 15) (pull 20 16)))

abbrev fourPulled (a : Data) (words rests : Fin 4 → List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        a.stacks 13 (words 0)) 14 (words 1)) 15 (words 2)) 16 (words 3))
      17 (rests 0)) 18 (rests 1)) 19 (rests 2)) 20 (rests 3)⟩

theorem pullFour_eval (a : Data) (words rests : Fin 4 → List Bool)
    (h0 : a.stacks 0 = []) (h4 : a.stacks 4 = []) (h10 : a.stacks 10 = [])
    (hd : ∀ i, a.stacks (target i) = [])
    (hs : ∀ i, a.stacks (source i) = words i ++ rests i)
    (hlen : ∀ i, (words i).length = (a.stacks 21).length) :
    Eval pullFour (56 * (a.stacks 21).length + 44) a (fourPulled a words rests) := by
  let a1 := pulled a 17 13 (words 0) (rests 0)
  let a2 := pulled a1 18 14 (words 1) (rests 1)
  let a3 := pulled a2 19 15 (words 2) (rests 2)
  have t0 := pull_eval a 17 13 (words 0) (rests 0)
    (by decide) (by decide) (by decide) h0 h4 h10 (hd 0) (hs 0) (hlen 0).symm
  have t1 := pull_eval a1 18 14 (words 1) (rests 1)
    (by decide) (by decide) (by decide)
    (by simp [a1, h0]) (by simp [a1, h4]) (by simp [a1, h10])
    (by simpa [a1, pulled, target] using hd 1)
    (by simpa [a1, pulled, source] using hs 1)
    (by simpa [a1, pulled] using (hlen 1).symm)
  have t2 := pull_eval a2 19 15 (words 2) (rests 2)
    (by decide) (by decide) (by decide)
    (by simp [a2, a1, h0]) (by simp [a2, a1, h4])
    (by simp [a2, a1, h10])
    (by simpa [a2, a1, pulled, target] using hd 2)
    (by simpa [a2, a1, pulled, source] using hs 2)
    (by simpa [a2, a1, pulled] using (hlen 2).symm)
  have t3 := pull_eval a3 20 16 (words 3) (rests 3)
    (by decide) (by decide) (by decide)
    (by simp [a3, a2, a1, h0]) (by simp [a3, a2, a1, h4])
    (by simp [a3, a2, a1, h10])
    (by simpa [a3, a2, a1, pulled, target] using hd 3)
    (by simpa [a3, a2, a1, pulled, source] using hs 3)
    (by simpa [a3, a2, a1, pulled] using (hlen 3).symm)
  have hfinish : pulled a3 20 16 (words 3) (rests 3) = fourPulled a words rests := by
    apply MatrixProgramSupport.data_ext
    · simp [ a3, a2, a1, readRegs_reset]
    · funext j
      fin_cases j <;> simp [ a3, a2, a1]
  rw [hfinish] at t3
  have he := t0.seq (t1.seq (t2.seq t3))
  convert he using 1
  rw [hlen 0, hlen 1, hlen 2, hlen 3]
  ring

theorem fourPulled_reg7 (a : Data) (words rests : Fin 4 → List Bool) :
    (fourPulled a words rests).regs 7 = a.regs 7 := by
  simp [ readRegs]

end SubexponentialSAT.Subexp.MatrixColorReadProgram

end OAI.Algorithms
