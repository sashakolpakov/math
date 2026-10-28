import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

/-! The proof shadow erases exactly the five suspended caller words. Actual
query sources, reusable workspace, reference and temporary bytes are retained.
No length premise is imposed on any erased word; this module constructs no
execution and changes no instruction table. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay

abbrev Data := State 40 896

/-- This is exactly the shadow used by the actual query's replay theorem. -/
def erase (a : Data) : Data :=
  rebaseState (fun i => i ∈ HighQueryProgram.Carried.words) (fun _ => []) a

@[simp] theorem erase_regs (a : Data) : (erase a).regs = a.regs := rfl

/-- Visible words retain their complete bit strings. -/
theorem visible (a : Data) (i : Fin 896) (hi : i ∉ HighQueryProgram.Carried.words) :
    (erase a).stacks i = a.stacks i :=
  rebaseStacks_of_not_mem (fun j => j ∈ HighQueryProgram.Carried.words)
    (fun _ => []) a.stacks i hi

/-- Erasure preserves an existing blank, whether or not the word is carried. -/
theorem blank (a : Data) (i : Fin 896) (hi : a.stacks i = []) :
    (erase a).stacks i = [] := by
  by_cases hm : i ∈ HighQueryProgram.Carried.words
  · exact rebaseStacks_of_mem (fun j => j ∈ HighQueryProgram.Carried.words)
      (fun _ => []) a.stacks i hm
  · exact (visible a i hm).trans hi

/-- The actual lower-bank clean-work predicate needs only its existing blanks. -/
theorem cleanWork (a : Data)
    (hc : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a)) :
    LeafProgram.Query.CleanWork (HighMarkedFrontend.project (erase a)) := by
  intro i hi h321
  exact blank a (HighMarkedFrontend.stackMap i) (hc i hi h321)

/-- All five immutable frontend source fields are visible to the shadow. -/
theorem sources (q : LeafQueryFrontend.Query) (a : Data)
    (hs : LeafProgram.Query.Sources q (HighMarkedFrontend.project a)) :
    LeafProgram.Query.Sources q (HighMarkedFrontend.project (erase a)) := by
  constructor
  · exact (visible a 700 (by decide)).trans hs.formula
  · exact (visible a 701 (by decide)).trans hs.rows
  · exact (visible a 707 (by decide)).trans hs.modulus
  · exact (visible a 708 (by decide)).trans hs.width
  · exact (visible a 709 (by decide)).trans hs.ambient

theorem reference (q : LeafQueryFrontend.Query) (a : Data)
    (href : a.stacks 321 = q.index.reverse) :
    (erase a).stacks 321 = q.index.reverse :=
  (visible a 321 (by decide)).trans href

theorem scratch (a : Data) (htmp : a.stacks 767 = []) :
    (erase a).stacks 767 = [] := blank a 767 htmp

/-- The marked return restores workspace outside the five collector ports.
In particular the actual reference321 is not required to be blank. -/
theorem marked_discarded (a : Data)
    (hd : ∀ i, HashMarkedReturn.kept i = false →
      (i.val < 320 ∨ 324 < i.val) → a.stacks i = []) :
    ∀ i, HashMarkedReturn.kept i = false →
      (i.val < 320 ∨ 324 < i.val) → (erase a).stacks i = [] :=
  fun i hi hout => blank a i (hd i hi hout)

/-- The accepted return retains its separate output788 exception. -/
theorem accepted_discarded (a : Data)
    (hd : ∀ i, i ≠ 788 → HashMarkedReturn.kept i = false → a.stacks i = []) :
    ∀ i, i ≠ 788 → HashMarkedReturn.kept i = false → (erase a).stacks i = [] :=
  fun i hi hk => blank a i (hd i hi hk)

/-- Only visible input bytes enter the local query width. -/
theorem word_bound (a : Data) (S : ℕ)
    (ha : ∀ i, i ∉ HighQueryProgram.Carried.words → (a.stacks i).length ≤ S) :
    ∀ i, ((erase a).stacks i).length ≤ S :=
  CommandStackTransport.shadow_stack_bound _ a S ha

/-- The literal predicate used by the actual staged-entry cap is the same
five-word shadow, including the two lower collector words. -/
theorem erase_eq_literal (a : Data) :
    erase a = rebaseState (fun i : Fin 896 => i.val = 320 ∨ i.val = 322 ∨
      i.val = 770 ∨ i.val = 771 ∨ i.val = 781) (fun _ => []) a := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    simp [rebaseStacks, HighQueryProgram.Carried.words,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod]

/-- The actual marked-record entry bounds its five retained words from the
real caller and collector fields. No candidate/history bound is needed here:
trial normalization changes768 and source staging changes only its six ports. -/
theorem record_hidden_bound (d a : Data) (m depth L : ℕ)
    (word tail bits : List Bool)
    (hd : ∀ i, (d.stacks i).length ≤ L)
    (hready : HashMassAdapter.Ready
      (fun ws => ws = HashMassAdapter.workspace
        (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d m depth word))) a)
    (hread : (HashMassAdapter.read a).length ≤ 3 * L + 2)
    (htail : tail.length ≤ 3 * L + 2) :
    ∀ i, i ∈ HighQueryProgram.Carried.words →
      ((RecordPrograms.state HashMassAdapter.recordPorts a false true false
        tail bits.reverse).stacks i).length ≤ 3 * L + 2 := by
  have frame (i : Fin 896) (hi : i = 770 ∨ i = 771 ∨ i = 781) :
      a.stacks i = d.stacks i := by
    have hn (j : Fin 896) (hj : j.val < 770) : i ≠ j := by
      intro he
      rcases hi with rfl | rfl | rfl <;> subst j <;> norm_num [Fin.coe_ofNat_eq_mod] at hj
    rw [HashMassAdapter.workspace_frame _ a hready.workspace_ready i
      (hn 320 (by decide)) (hn 321 (by decide)) (hn 322 (by decide))
      (hn 323 (by decide)) (hn 324 (by decide))]
    rw [HashMassStaged.staged_frame _ i (by rcases hi with rfl | rfl | rfl <;> decide)]
    exact Function.update_of_ne (hn 768 (by decide)) _ _
  intro i hi
  simp only [HighQueryProgram.Carried.words, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · simpa [RecordPrograms.state, HashMassAdapter.recordPorts] using htail
  · simpa [RecordPrograms.state, HashMassAdapter.recordPorts, HashMassAdapter.read] using hread
  · simpa only [RecordPrograms.state, HashMassAdapter.recordPorts,
      Function.update_of_ne (by decide : (770 : Fin 896) ≠ 321),
      Function.update_of_ne (by decide : (770 : Fin 896) ≠ 320),
      frame 770 (Or.inl rfl)] using (hd 770).trans (by omega : L ≤ 3 * L + 2)
  · simpa only [RecordPrograms.state, HashMassAdapter.recordPorts,
      Function.update_of_ne (by decide : (771 : Fin 896) ≠ 321),
      Function.update_of_ne (by decide : (771 : Fin 896) ≠ 320),
      frame 771 (Or.inr (Or.inl rfl))] using (hd 771).trans (by omega : L ≤ 3 * L + 2)
  · simpa only [RecordPrograms.state, HashMassAdapter.recordPorts,
      Function.update_of_ne (by decide : (781 : Fin 896) ≠ 321),
      Function.update_of_ne (by decide : (781 : Fin 896) ≠ 320),
      frame 781 (Or.inr (Or.inr rfl))] using (hd 781).trans (by omega : L ≤ 3 * L + 2)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow
