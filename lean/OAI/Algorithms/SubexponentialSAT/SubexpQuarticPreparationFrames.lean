import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticInitialCalls
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticTupleCalls

namespace OAI.Algorithms

/-! # Workspace frames during actual quartic-table preparation -/

namespace SubexponentialSAT.SubexpQuarticPreparationFrames

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 14 35

def Blank (occupied : List (Fin 35)) (d : Data) : Prop :=
  ∀ j, j ∉ occupied → d.stacks j = []

theorem blank_copy (occupied : List (Fin 35)) (d : Data) (src dst : Fin 35)
    (h : Blank occupied d) : Blank (dst :: occupied) (afterCopy d src dst 0 1) := by
  intro j hj
  have hne : j ≠ dst := by intro he; apply hj; simp [he]
  have hn : j ∉ occupied := by intro hm; apply hj; simp [hm]
  exact (StackRoutines.copyStacks_frame src dst j d.stacks hne).trans (h j hn)

theorem blank_normalized (d next : Data) (hd : Blank [34] d)
    (h0 : next.stacks 0 = []) (h1 : next.stacks 1 = [])
    (hf : ∀ j : Fin 35, j ≠ 34 → j ≠ 0 → j ≠ 1 → next.stacks j = d.stacks j) :
    Blank [34] next := by
  intro j hj
  by_cases hj0 : j = 0
  · simpa only [hj0] using h0
  by_cases hj1 : j = 1
  · simpa only [hj1] using h1
  exact (hf j (by simpa using hj) hj0 hj1).trans (hd j hj)

theorem blank_alphabet (d next : Data) (hd : Blank [31, 19, 34] d)
    (h0 : next.stacks 0 = []) (h1 : next.stacks 1 = [])
    (h2 : next.stacks 2 = []) (h22 : next.stacks 22 = [])
    (hf : ∀ j : Fin 35, j ≠ 34 → j ≠ 22 → j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 25 →
      next.stacks j = d.stacks j) : Blank [25, 31, 19, 34] next := by
  intro j hj
  by_cases hj0 : j = 0
  · simpa only [hj0] using h0
  by_cases hj1 : j = 1
  · simpa only [hj1] using h1
  by_cases hj2 : j = 2
  · simpa only [hj2] using h2
  by_cases hj22 : j = 22
  · simpa only [hj22] using h22
  have hj34 : j ≠ 34 := by intro he; apply hj; simp [he]
  have hj25 : j ≠ 25 := by intro he; apply hj; simp [he]
  have hn : j ∉ [31, 19, 34] := by intro hm; apply hj; simp [hm]
  exact (hf j hj34 hj22 hj0 hj1 hj2 hj25).trans (hd j hn)

def afterMarkerClear (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 3 d.stacks⟩

theorem clear_marker_eval (d : Data) (h3 : d.stacks 3 = [false]) :
    Eval (.call (StackRoutines.clearProgram (3 : Fin 35) (0 : Fin 14) 1))
      5 d (afterMarkerClear d) := by
  have h := Subexp.TupleProgram.clear_eval (3 : Fin 35) (0 : Fin 14) 1 d
  simpa only [h3, List.length_cons, List.length_nil, afterMarkerClear] using h

theorem afterMarkerClear_frame (d : Data) (j : Fin 35) (hj : j ≠ 3) :
    (afterMarkerClear d).stacks j = d.stacks j :=
  StackRoutines.clearStacks_frame 3 j d.stacks hj

theorem not_mem_of_small (occupied : List (Fin 35))
    (hh : ∀ j ∈ occupied, 7 ≤ j.val) (i : Fin 35) (hi : i.val < 7) : i ∉ occupied := by
  intro hm
  have := hh i hm
  omega

theorem tuple_input (occupied : List (Fin 35)) (d : Data) (destination : Fin 35)
    (alphabet : List (List Bool)) (hd : Blank occupied d)
    (hh : ∀ j ∈ occupied, 7 ≤ j.val) (houtput : destination ∉ occupied)
    (ha : d.stacks 25 = ProgramEncoding.encodeRecords alphabet) :
    SubexpQuarticTupleCalls.Input destination alphabet d := by
  refine ⟨hd destination houtput, ha, ?_, ?_⟩
  · exact ⟨hd 0 (not_mem_of_small occupied hh 0 (by decide)),
      hd 1 (not_mem_of_small occupied hh 1 (by decide)),
      hd 2 (not_mem_of_small occupied hh 2 (by decide)),
      hd 4 (not_mem_of_small occupied hh 4 (by decide)),
      hd 5 (not_mem_of_small occupied hh 5 (by decide))⟩
  · exact hd 3 (not_mem_of_small occupied hh 3 (by decide))

theorem blank_tuple (occupied : List (Fin 35)) (d next : Data)
    (n : ℕ) (destination : Fin 35) (alphabet : List (List Bool))
    (hd : Blank occupied d) (hh : ∀ j ∈ occupied, 7 ≤ j.val) (h25 : (25 : Fin 35) ∈ occupied)
    (hc : SubexpQuarticTupleCalls.Completed n destination alphabet d next) :
    Blank (destination :: occupied) (afterMarkerClear next) := by
  intro j hj
  by_cases hj3 : j = 3
  · subst j
    exact StackRoutines.clearStacks_src 3 next.stacks
  rw [afterMarkerClear_frame next j hj3]
  by_cases hsmall : j.val < 7
  · have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases hcases with h | h | h | h | h | h | h
    · simpa only [h] using hc.clean.1
    · simpa only [h] using hc.clean.2.1
    · simpa only [h] using hc.clean.2.2.1
    · exact (hj3 h).elim
    · simpa only [h] using hc.clean.2.2.2.1
    · simpa only [h] using hc.clean.2.2.2.2
    · rw [h, hc.depth]
      exact hd 6 (not_mem_of_small occupied hh 6 (by decide))
  · have hdest : j ≠ destination := by intro he; apply hj; simp [he]
    have hn : j ∉ occupied := by intro hm; apply hj; simp [hm]
    have hj25 : j ≠ 25 := by intro he; exact hn (he.symm ▸ h25)
    exact (hc.stack_frame j (by omega) hj25 hdest).trans (hd j hn)

end SubexponentialSAT.SubexpQuarticPreparationFrames

end OAI.Algorithms
