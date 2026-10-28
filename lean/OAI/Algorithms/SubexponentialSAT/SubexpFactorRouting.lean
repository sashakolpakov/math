import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingTraversal
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingSetup

namespace OAI.Algorithms

/-! An actual assignment-driven stable filter of original factor packets. -/

namespace SubexponentialSAT.SubexpFactorRouting

open BitProgram StructuredCalls SubexpFactorRoutingControl SubexpFactorRoutingCalls
open SubexpFactorRoutingCallback SubexpFactorRoutingTraversal SubexpFactorRoutingSetup

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The bound counts the concrete copy, conversion, parser, comparison,
emitter, reversal, and cleanup instructions used by the fixed program. -/
def runtime {r Q : ℕ} (d : Data) (t : Fin Q) (g : Fin r)
    (items : List (Item r Q)) (suffix : List Bool) : ℕ :=
  prepareBudget d + (2 + budget (Q * r) t.val r g.val items) +
    (10 * (Encoding.encodeList id (retained t g items).reverse).length +
      2 * suffix.length + 2 * g.val + 2 * t.val + 25) + 1

theorem prepared_workClean (d a : Data) (hc : Clean d)
    (ha : a.stacks = preparedStacks d) : WorkClean a := by
  intro i hi
  rw [ha]
  simp only [workPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simpa [preparedStacks] using hc _ (by decide)

/-- Both streams are consumed in their original order. Each keep/drop
decision is proved from the matching assignment word read by the machine. -/
theorem program_runs {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (Item r Q)) (suffix : List Bool) (d : Data)
    (hc : Clean d)
    (h0 : d.stacks 0 = words items ++ suffix)
    (h1 : d.stacks 1 = Encoding.encodeList id (items.map Prod.snd))
    (h2 : CounterPrograms.value (d.stacks 2) = g.val)
    (h3 : d.stacks 3 = unary t.val) (h4 : d.stacks 4 = unary r)
    (h5 : (d.stacks 5).length = Q * r) :
    RunsIn program (runtime d t g items suffix)
      (d.withPC (some program.entry))
      ((result d (Encoding.encodeList id (retained t g items))).withPC none) := by
  obtain ⟨np, hnp, a, hp, ha⟩ := prepare_eval d hc
  have hac : WorkClean a := prepared_workClean d a hc ha
  have ha4 : a.stacks 4 = unary r := by simpa [ha, preparedStacks] using h4
  have ha5 : (a.stacks 5).length = Q * r := by simpa [ha, preparedStacks] using h5
  have ha12 : a.stacks 12 = unary g.val := by simp [ha, preparedStacks, h2]
  have ha13 : a.stacks 13 = unary t.val := by simp [ha, preparedStacks, h3]
  have ha7 : a.stacks 7 = words items ++ suffix := by simp [ha, preparedStacks, h0]
  have ha8 : a.stacks 8 = Encoding.encodeList id (items.map Prod.snd) := by
    simp [ha, preparedStacks, h1]
  have ha9 : a.stacks 9 = [] := by simpa [ha, preparedStacks] using hc 9 (by decide)
  obtain ⟨ni, hni, b, hi, hb7, hb8, hb9, hb23, hf⟩ :=
    iterate_eval t g items suffix a hac ha4 ha5 ha12 ha13 ha7 ha8 ha9
  have hb6 : b.stacks 6 = [false] := by
    rw [hf 6 (by decide) (by decide) (by decide) (by decide), ha]
    simp [preparedStacks]
  have hb12 : b.stacks 12 = unary g.val :=
    (hf 12 (by decide) (by decide) (by decide) (by decide)).trans ha12
  have hb13 : b.stacks 13 = unary t.val :=
    (hf 13 (by decide) (by decide) (by decide) (by decide)).trans ha13
  have hb28 : b.stacks 28 = [] := by
    rw [hf 28 (by decide) (by decide) (by decide) (by decide), ha]
    simpa [preparedStacks] using hc 28 (by decide)
  have hb23' : b.stacks 23 = Encoding.encodeList id (retained t g items).reverse := by
    rw [hb23]
    have ha23 : a.stacks 23 = Encoding.encodeList id [] := by simp [ha, preparedStacks, Encoding.encodeList]
    rw [ha23, accumulate_encoded]
    simp only [List.append_nil]
  obtain ⟨nf, hnf, hfinish⟩ := finish_eval b (retained t g items).reverse hb6 hb23' hb28
  have hs : finishedStacks b (retained t g items).reverse =
      Function.update d.stacks 6 (Encoding.encodeList id (retained t g items)) := by
    funext i
    by_cases h6 : i = 6
    · subst i
      simp [finishedStacks]
    by_cases h7 : i = 7
    · subst i
      simp [finishedStacks, hc 7 (by decide)]
    by_cases h8 : i = 8
    · subst i
      simp [finishedStacks, hb8, hc 8 (by decide)]
    by_cases h9 : i = 9
    · subst i
      simp [finishedStacks, hb9, hc 9 (by decide)]
    by_cases h12 : i = 12
    · subst i
      simp [finishedStacks, hc 12 (by decide)]
    by_cases h13 : i = 13
    · subst i
      simp [finishedStacks, hc 13 (by decide)]
    by_cases h23 : i = 23
    · subst i
      simp [finishedStacks, hc 23 (by decide)]
    have hbi := hf i h7 h8 h9 h23
    rw [ha] at hbi
    simpa [finishedStacks, preparedStacks, h6, h7, h8, h9, h12, h13, h23] using hbi
  have hout : (⟨fun _ => false, finishedStacks b (retained t g items).reverse⟩ : Data) =
      result d (Encoding.encodeList id (retained t g items)) := SubexpScanPrimitives.state_ext rfl hs
  rw [hout] at hfinish
  have he := hp.seq (hi.seq hfinish)
  change Eval command (np + (ni + nf)) d
    (result d (Encoding.encodeList id (retained t g items))) at he
  refine ⟨np + (ni + nf) + 1, ?_, compiled_halt_trace he 0 6⟩
  rw [hb7, hb12, hb13, List.length_replicate, List.length_replicate] at hnf
  unfold runtime
  omega

end SubexponentialSAT.SubexpFactorRouting

end OAI.Algorithms
