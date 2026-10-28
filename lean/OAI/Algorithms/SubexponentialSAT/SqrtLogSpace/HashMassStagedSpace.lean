import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace

/-! Physical staging, all marked counts, and actual source cleanup share one
prefix bound. Cleanup only removes bits, so it does not amplify the query's
transient cap into the next boundary allowance. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter HashMassStaged

/-- The caller cap L is distinct from the staged boundary cap 3*L+2. -/
def spaceBudget (a : State 40 896) (L K : ℕ) : ℕ :=
  max K (896 * (3 * L + 2) +
    (LeafOuterProgram.routeCost (782,0) a + LeafOuterNative.References.budget (a.stacks 782) + 1) +
      50 * (3 * L + 3) + 59 * L + 100)

/-- The explicit staging/reference expression is bounded by one fixed cube;
the expensive query contributes only its independently proved prefix cap. -/
theorem spaceBudget_le (a : State 40 896) (m L K : ℕ)
    (hm : CounterPrograms.value (a.stacks 782) = m)
    (hL : ∀ i, (a.stacks i).length ≤ L) :
    spaceBudget a L K ≤ max K (10000 * (m + L + 1) ^ 3) := by
  let S := m + L + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hLS : L ≤ S := by dsimp [S]; omega
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have href := HashMassBounds.massBudget_le a (fun _ => 0) (fun _ => 0) m 0 L 0 hm
    (hL 0) (hL 782) (hL 769) (by intro; exact Nat.zero_le _) (by intro; exact Nat.zero_le _)
  have href' : LeafOuterProgram.routeCost (782,0) a +
      LeafOuterNative.References.budget (a.stacks 782) + 1 ≤ 1000 * S ^ 3 := by
    have hbase : LeafOuterProgram.routeCost (782,0) a +
        LeafOuterNative.References.budget (a.stacks 782) + 1 ≤
        massBudget a (fun _ => 0) (fun _ => 0) m := by
      unfold massBudget
      omega
    exact hbase.trans (by simpa [S] using href)
  unfold spaceBudget
  apply max_le_max le_rfl
  change _ ≤ 10000 * S ^ 3
  nlinarith

theorem command_halt_space (query : Cmd 40 896) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : State 40 896) (m L K : ℕ)
    (ha : ReferencesReady a) (hm : CounterPrograms.value (a.stacks 782) = m)
    (hL : ∀ i, (a.stacks i).length ≤ L)
    (hcollector : ∀ i : Fin 896, 321 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (hvalid : ∀ e : Fin m, valid (Encoding.encodeNat e.val))
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth width (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hq : ∀ bits tail (base : State 40 896), valid bits →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged a)) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace (LeafOuterNative.trialStaged a) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged a)) base →
      (read base).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      bits.length ≤ 3 * L + 2 → width bits ≤ 3 * L + 2 →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    {steps : ℕ} {result : State 40 896} (he : Eval (HashMassStaged.command query) steps a result) :
    StageSpace (HashMassStaged.command query) (steps + 1) a (spaceBudget a L K) := by
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
          rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        · decide
      rw [staged_frame a i hne]
      exact ha.empty i hi
  obtain ⟨nc, _, c, hc, hout⟩ := mass_eval query count queryCost width valid s m hs
    (by rw [staged_frame a 782 (by decide)]; exact hm)
    (by rw [staged_frame a 321 (by decide)]; exact hcollector 321 (by decide) (by decide))
    (by rw [staged_frame a 322 (by decide)]; exact hcollector 322 (by decide) (by decide))
    (by rw [staged_frame a 323 (by decide)]; exact hcollector 323 (by decide) (by decide))
    (by rw [staged_frame a 324 (by decide)]; exact hcollector 324 (by decide) (by decide)) hvalid hq
  have hmassSpace := HashMassSpace.mass_halt_space query count queryCost width valid s m
    (3 * L + 2) K hs (by rw [staged_frame a 782 (by decide)]; exact hm)
    (staged_stack_bound a L hL)
    (by rw [staged_frame a 321 (by decide)]; exact hcollector 321 (by decide) (by decide))
    (by rw [staged_frame a 322 (by decide)]; exact hcollector 322 (by decide) (by decide))
    (by rw [staged_frame a 323 (by decide)]; exact hcollector 323 (by decide) (by decide))
    (by rw [staged_frame a 324 (by decide)]; exact hcollector 324 (by decide) (by decide))
    hvalid href hgrowth hq hspace hc
  have hmass : StageSpace (mass query) (nc + 1) s (spaceBudget a L K) := by
    constructor
    intro k state hk ht i
    have h := hmassSpace.bound k state hk ht i
    have hroute : LeafOuterProgram.routeCost (782,0) s = LeafOuterProgram.routeCost (782,0) a := by
      dsimp only [s]
      simp only [LeafOuterProgram.routeCost, staged_frame a 0 (by decide),
        staged_frame a 782 (by decide)]
    have h782 : s.stacks 782 = a.stacks 782 := staged_frame a 782 (by decide)
    rw [hroute, h782] at h
    unfold spaceBudget
    omega
  have hcBound : ∀ i, (c.stacks i).length ≤ spaceBudget a L K := by
    intro i
    exact hmass.bound (nc + 1) (c.withPC none) le_rfl (compiled_halt_trace hc 778 777) i
  have hc767 : c.stacks 767 = [] := by simp [hout, hs.scratch]
  have hclean := cleanup_eval c hc767
  have hcleanSpace : StageSpace cleanup (cleanupCost c) c (spaceBudget a L K) := by
    constructor
    simpa only [cleanup, cleanupCost, stagedPorts, List.length_cons, List.length_nil] using
      HighQuerySpace.clear_bank_bound (767 : Fin 896) (0 : Fin 40) 1 stagedPorts
        (by decide) c hc767 (spaceBudget a L K) hcBound 778 777
  have hstage := LeafOuterNative.stageTrial_eval a ha.scratch
  have hstageSpace : StageSpace LeafOuterNative.stageTrial (LeafOuterNative.stageTrialCost a) a
      (spaceBudget a L K) := by
    constructor
    intro k state hk ht i
    have h := StructuredSpace.local_stack_bound (compiled LeafOuterNative.stageTrial 778 777)
      (StreamResources.dataBits_le_mul _ hL) k state (hk.trans (stage_cost_le a L hL)) ht i
    unfold spaceBudget
    omega
  have hmassNoHalt : StageSpace (mass query) nc s (spaceBudget a L K) := by
    constructor
    intro k state hk ht i
    exact hmass.bound k state (by omega) ht i
  have hfull := hstage.seq (hc.seq hclean)
  have hfullSpace := StageSpace.seq hstage (hc.seq hclean) hstageSpace
    (StageSpace.seq hc hclean hmassNoHalt hcleanSpace)
  have hsteps := StreamResources.eval_steps_eq 778 777 he hfull
  rw [hsteps]
  exact ⟨StructuredSpace.compiled_halt_stack_bound hfull 778 777 hfullSpace.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace
