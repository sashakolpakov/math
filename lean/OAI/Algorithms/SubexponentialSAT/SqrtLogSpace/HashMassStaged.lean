import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashTrialStage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram LeafOuterProgram
open HashMassAdapter

/-- These are exactly the lower ports changed by the original trial staging. -/
def stagedPorts : List (Fin 896) := [700,701,702,707,708,709]
def cleanup : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 stagedPorts
def cleaned (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks stagedPorts a.stacks⟩
def cleanupCost (a : State 40 896) : ℕ :=
  2 * (stagedPorts.map fun i => (a.stacks i).length).sum + 21

def command (query : Cmd 40 896) : Cmd 40 896 :=
  .seq LeafOuterNative.stageTrial (.seq (mass query) cleanup)

def stagingBudget (a : State 40 896) : ℕ :=
  LeafOuterNative.stageTrialCost a + cleanupCost (LeafOuterNative.trialStaged a)
def budget (a : State 40 896) (queryCost width : List Bool → ℕ) (m : ℕ) : ℕ :=
  stagingBudget a + massBudget a queryCost width m

theorem cleanup_eval (a : State 40 896) (ht : a.stacks 767 = []) :
    Eval cleanup (cleanupCost a) a (cleaned a) := by
  simpa only [cleanup, cleanupCost, cleaned, stagedPorts, List.length_cons, List.length_nil] using
    BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 stagedPorts (by decide) a.regs a.stacks ht

theorem staged_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ stagedPorts) :
    (LeafOuterNative.trialStaged a).stacks i = a.stacks i := by
  have hne : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [stagedPorts] using hi
  exact LeafOuterNative.trialStaged_frame a i hne.1 hne.2.1 hne.2.2.1
    hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2

theorem staged_stacks_congr (a b : State 40 896) (h : a.stacks = b.stacks) :
    (LeafOuterNative.trialStaged a).stacks = (LeafOuterNative.trialStaged b).stacks := by
  funext i
  have ha := LeafOuterNative.trialStaged_sources a
  have hb := LeafOuterNative.trialStaged_sources b
  by_cases hi : i ∈ stagedPorts
  · simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [ha.1,hb.1,h]
    · rw [ha.2.1,hb.2.1,h]
    · exact (LeafOuterNative.prefixed_scratch _).trans (LeafOuterNative.prefixed_scratch _).symm
    · rw [ha.2.2.1,hb.2.2.1,h]
    · rw [ha.2.2.2.1,hb.2.2.2.1,h]
    · rw [ha.2.2.2.2,hb.2.2.2.2,h]
  · rw [staged_frame a i hi,staged_frame b i hi,h]

/-- This literal equality is the missing candidate/history assembler bridge. -/
theorem staged_rows (a : State 40 896) (rows : List (List Bool))
    (hh : a.stacks 777 = HashGreedyProgram.encodedHistory rows) :
    (LeafOuterNative.trialStaged a).stacks 701 =
      HashGreedyProgram.encodedHistory (a.stacks 768 :: rows) := by
  rw [(LeafOuterNative.trialStaged_sources a).2.1, hh]
  rfl

/-- The inner mass collector sees the physically staged sources. After all
marked counts have been added, actual cleanup restores every source master. -/
theorem eval (query : Cmd 40 896) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : State 40 896) (m : ℕ)
    (ha : ReferencesReady a) (hm : CounterPrograms.value (a.stacks 782) = m)
    (hcollector : ∀ i : Fin 896, 321 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (hempty : ∀ i ∈ stagedPorts, a.stacks i = [])
    (hvalid : ∀ e : Fin m, valid (Encoding.encodeNat e.val))
    (hq : ∀ bits tail (base : State 40 896), valid bits →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged a)) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace (LeafOuterNative.trialStaged a) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ n ≤ budget a queryCost width m, ∃ b, Eval (command query) n a b ∧
      b.stacks = Function.update a.stacks 769
        (DisjointReuse.binaryNat (((RowSelectionProgram.Index.alphabet m).map count).sum)) := by
  let s := LeafOuterNative.trialStaged a
  have hs : ReferencesReady s := by
    constructor
    · rw [staged_frame a 767 (by decide)]
      exact ha.scratch
    · intro i hi
      have hne : i ∉ stagedPorts := by
        simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at *
        rcases hi with hi | rfl
        · intro hh
          rcases hh with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
        · decide
      rw [staged_frame a i hne]
      exact ha.empty i hi
  obtain ⟨nc, hnc, c, hc, hout⟩ := mass_eval query count queryCost width valid s m hs
    (by rw [staged_frame a 782 (by decide)]; exact hm)
    (by rw [staged_frame a 321 (by decide)]; exact hcollector 321 (by decide) (by decide))
    (by rw [staged_frame a 322 (by decide)]; exact hcollector 322 (by decide) (by decide))
    (by rw [staged_frame a 323 (by decide)]; exact hcollector 323 (by decide) (by decide))
    (by rw [staged_frame a 324 (by decide)]; exact hcollector 324 (by decide) (by decide)) hvalid hq
  have hc767 : c.stacks 767 = [] := by simp [hout, hs.scratch]
  have hcost : cleanupCost c = cleanupCost s := by
    unfold cleanupCost
    congr 2
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ 769 := by
      simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp [hout, hne]
  have hbudget : massBudget s queryCost width m = massBudget a queryCost width m := by
    simp only [s, massBudget, routeCost, staged_frame a 0 (by decide),
      staged_frame a 782 (by decide), staged_frame a 769 (by decide)]
  refine ⟨LeafOuterNative.stageTrialCost a + (nc + cleanupCost c), ?_, cleaned c,
    (LeafOuterNative.stageTrial_eval a ha.scratch).seq (hc.seq (cleanup_eval c hc767)), ?_⟩
  · rw [hcost]
    rw [hbudget] at hnc
    change LeafOuterNative.stageTrialCost a + (nc + cleanupCost s) ≤
      LeafOuterNative.stageTrialCost a + cleanupCost s + massBudget a queryCost width m
    omega
  funext i
  by_cases hi : i ∈ stagedPorts
  · have hne : i ≠ 769 := by
      simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp [cleaned, BankRoutines.clearBankStacks, hi, hne, hempty i hi]
  · simp only [cleaned, BankRoutines.clearBankStacks, ite_eq_right hi, hout]
    by_cases h769 : i = 769
    · subst i; simp
    · simp only [Function.update_of_ne h769]
      exact staged_frame a i hi

/-- Literal cost formula: only the six overwritten sources, the five copied
masters/history words, and the current candidate contribute. -/
theorem stagingBudget_eq (a : State 40 896) :
    stagingBudget a =
      2 * ((a.stacks 700).length + (a.stacks 701).length + (a.stacks 702).length +
        (a.stacks 707).length + (a.stacks 708).length + (a.stacks 709).length) +
      9 * ((a.stacks 777).length + (a.stacks 782).length + (a.stacks 783).length +
        (a.stacks 784).length + (a.stacks 785).length) + 16 * (a.stacks 768).length + 83 := by
  have h := LeafOuterNative.trialStaged_sources a
  have h702 : (LeafOuterNative.trialStaged a).stacks 702 = [] :=
    LeafOuterNative.prefixed_scratch _
  unfold stagingBudget cleanupCost
  simp only [stagedPorts,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,h702,List.length_cons,List.length_nil,
    List.length_append,Encoding.length_frame,List.length_reverse]
  simp [LeafOuterNative.stageTrialCost,LeafOuterNative.stageFinalCost,
    LeafOuterNative.prefixCost,LeafOuterNative.finalStaged,LeafOuterNative.masterRoutes,
    routesCost,routesState,routed,routeCost]
  ring

theorem stagingBudget_le_sources (a : State 40 896) (L : ℕ)
    (hempty : ∀ i ∈ stagedPorts, a.stacks i = [])
    (hsource : ∀ i ∈ ([777,782,783,784,785] : List (Fin 896)), (a.stacks i).length ≤ L)
    (hcandidate : (a.stacks 768).length ≤ L) : stagingBudget a ≤ 95 * L + 103 := by
  have h777 := hsource 777 (by simp)
  have h782 := hsource 782 (by simp)
  have h783 := hsource 783 (by simp)
  have h784 := hsource 784 (by simp)
  have h785 := hsource 785 (by simp)
  rw [stagingBudget_eq]
  simp only [hempty 700 (by simp [stagedPorts]),hempty 701 (by simp [stagedPorts]),
    hempty 702 (by simp [stagedPorts]),hempty 707 (by simp [stagedPorts]),
    hempty 708 (by simp [stagedPorts]),hempty 709 (by simp [stagedPorts]),List.length_nil]
  omega

theorem staged_stack_bound (a : State 40 896) (L : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ L) :
    ∀ i, ((LeafOuterNative.trialStaged a).stacks i).length ≤ 3 * L + 2 := by
  intro i
  have hsrc := LeafOuterNative.trialStaged_sources a
  by_cases hi : i ∈ stagedPorts
  · simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [hsrc.1]; have := ha 784; omega
    · rw [hsrc.2.1]
      simp only [List.length_cons,List.length_append,Encoding.length_frame,List.length_reverse]
      have := ha 768
      have := ha 777
      omega
    · rw [show (LeafOuterNative.trialStaged a).stacks 702 = [] from
        LeafOuterNative.prefixed_scratch _]
      simp
    · rw [hsrc.2.2.1]; have := ha 782; omega
    · rw [hsrc.2.2.2.1]; have := ha 783; omega
    · rw [hsrc.2.2.2.2]; have := ha 785; omega
  · rw [staged_frame a i hi]
    have := ha i
    omega

theorem stage_cost_le (a : State 40 896) (L : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ L) :
    LeafOuterNative.stageTrialCost a ≤ 59 * L + 58 := by
  have hf := routes_cost_bound LeafOuterNative.masterRoutes a L ha
  have h702 := LeafOuterNative.finalStaged_frame a 702 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h768 := LeafOuterNative.finalStaged_frame a 768 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h1 := ha 702
  have h2 := ha 768
  unfold LeafOuterNative.stageTrialCost LeafOuterNative.stageFinalCost
    LeafOuterNative.prefixCost routeCost
  rw [h702,h768]
  simp only [LeafOuterNative.masterRoutes,List.length_cons,List.length_nil] at hf ⊢
  omega

theorem stagingBudget_le (a : State 40 896) (L : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ L) : stagingBudget a ≤ 95 * L + 103 := by
  have hs := stage_cost_le a L ha
  have hb := staged_stack_bound a L ha
  have hc : (stagedPorts.map fun i => ((LeafOuterNative.trialStaged a).stacks i).length).sum ≤
      6 * (3 * L + 2) := by
    have h := List.sum_le_length_nsmul
      (stagedPorts.map fun i => ((LeafOuterNative.trialStaged a).stacks i).length) (3 * L + 2)
      (by intro x hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact hb i)
    simpa [stagedPorts] using h
  unfold stagingBudget cleanupCost
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
