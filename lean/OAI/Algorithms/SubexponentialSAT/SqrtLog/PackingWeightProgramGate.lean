import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgramGateBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def choose : Code := .ite 3 (.base .skip) (copy 1 2)

theorem choose_eval (d : Data) (h2 : d.stacks 2 = []) (h6 : d.stacks 6 = []) :
    ∃ t ≤ 7 * (d.stacks 1).length + 6, ∃ e : Data,
      Eval choose t d e ∧
      e.stacks 2 = (if d.regs 3 then [] else d.stacks 1) ∧
      (∀ j, j ≠ 2 → e.stacks j = d.stacks j) := by
  cases hr : d.regs 3 with
  | true =>
      exact ⟨1, by omega, d, .ite_true hr (.base (.skip d)), by simp [ h2],
        fun _ _ => rfl⟩
  | false =>
      refine ⟨7 * (d.stacks 1).length + 5 + 1, by omega, copied d 1 2,
        .ite_false hr (copy_eval d 1 2 (by decide) (by decide) (by decide) h6), ?_, ?_⟩
      · simp [copied, StackRoutines.copyStacks, h2]
      · intro j hj; simp [copied, StackRoutines.copyStacks, hj]

/-- Binary n on0; arbitrary processed-count word on1. Only output2 changes. -/
def command : Code := .seq (copy 0 3) (.seq convert (.seq (copy 1 5)
  (.seq compare (.seq choose (.seq (clear 4) (clear 5))))))
def program := compiled command 0 2
def ready (d : Data) : Prop := ∀ j : Fin 7, 2 ≤ j.val → d.stacks j = []
def output (d : Data) : List Bool :=
  if (d.stacks 1).length < CounterPrograms.value (d.stacks 0) then d.stacks 1 else []
def budget (d : Data) : ℕ := CounterConversions.runtimeBound (d.stacks 0) +
  7 * (d.stacks 0).length + 20 * (d.stacks 1).length +
  2 * CounterPrograms.value (d.stacks 0) + 30

theorem command_eval (d : Data) (hd : ready d) :
    ∃ t ≤ budget d, ∃ z : Data, Eval command t d z ∧ z.stacks 2 = output d ∧
      (∀ j, j ≠ 2 → z.stacks j = d.stacks j) := by
  let a := copied d 0 3
  have ha := copy_eval d 0 3 (by decide) (by decide) (by decide) (hd 6 (by decide))
  have ha3 : a.stacks 3 = d.stacks 0 := by simp [a, copied, StackRoutines.copyStacks, hd 3 (by decide)]
  have haf (j : Fin 7) (hj : j ≠ 3) : a.stacks j = d.stacks j := by
    simp [a, copied, StackRoutines.copyStacks, hj]
  obtain ⟨tu, htu, b, hu, hb3, hb4, hbf⟩ := convert_eval a
    ((haf 4 (by decide)).trans (hd 4 (by decide)))
    ((haf 6 (by decide)).trans (hd 6 (by decide)))
  rw [ha3] at htu hb4
  have hb1 : b.stacks 1 = d.stacks 1 := (hbf 1 (by decide) (by decide)).trans (haf 1 (by decide))
  have hb2 : b.stacks 2 = [] := (hbf 2 (by decide) (by decide)).trans
    ((haf 2 (by decide)).trans (hd 2 (by decide)))
  have hb5 : b.stacks 5 = [] := (hbf 5 (by decide) (by decide)).trans
    ((haf 5 (by decide)).trans (hd 5 (by decide)))
  have hb6 : b.stacks 6 = [] := (hbf 6 (by decide) (by decide)).trans
    ((haf 6 (by decide)).trans (hd 6 (by decide)))
  let c := copied b 1 5
  have hc := copy_eval b 1 5 (by decide) (by decide) (by decide) hb6
  have hcf (j : Fin 7) (hj : j ≠ 5) : c.stacks j = b.stacks j := by
    simp [c, copied, StackRoutines.copyStacks, hj]
  have hc4 : (c.stacks 4).length = CounterPrograms.value (d.stacks 0) := by
    rw [hcf 4 (by decide), hb4]; simp
  have hc5 : c.stacks 5 = d.stacks 1 := by
    simp [c, copied, StackRoutines.copyStacks, hb5, hb1]
  obtain ⟨tc, htc, e, he, her, he4, he5, hef⟩ := compare_eval c
  simp only [hc4, hc5] at htc her he4 he5
  have he1 : e.stacks 1 = d.stacks 1 := (hef 1 (by decide) (by decide)).trans
    ((hcf 1 (by decide)).trans hb1)
  have he2 : e.stacks 2 = [] := (hef 2 (by decide) (by decide)).trans
    ((hcf 2 (by decide)).trans hb2)
  have he6 : e.stacks 6 = [] := (hef 6 (by decide) (by decide)).trans
    ((hcf 6 (by decide)).trans hb6)
  obtain ⟨ts, hts, f, hs, hf2, hff⟩ := choose_eval e he2 he6
  rw [he1] at hts
  have hf4 : (f.stacks 4).length ≤ CounterPrograms.value (d.stacks 0) := by
    rw [hff 4 (by decide)]; exact he4
  have hf5 : (f.stacks 5).length ≤ (d.stacks 1).length := by
    rw [hff 5 (by decide)]; exact he5
  let g := cleared f 4
  let z := cleared g 5
  have hg := clear_eval f 4
  have hz := clear_eval g 5
  have hg5 : g.stacks 5 = f.stacks 5 := by simp [g, cleared]
  refine ⟨(7 * (d.stacks 0).length + 5) + (tu +
    ((7 * (b.stacks 1).length + 5) + (tc + (ts +
      ((2 * (f.stacks 4).length + 3) + (2 * (g.stacks 5).length + 3)))))),
    ?_, z, ha.seq (hu.seq (hc.seq (he.seq (hs.seq (hg.seq hz))))), ?_, ?_⟩
  · rw [hb1, hg5]
    have hm := Nat.min_le_right (CounterPrograms.value (d.stacks 0)) (d.stacks 1).length
    unfold budget
    omega
  · have hout : f.stacks 2 = output d := by
      rw [hf2, her, he1]
      unfold output
      by_cases h : (d.stacks 1).length < CounterPrograms.value (d.stacks 0)
      · simp [h, Nat.not_le.mpr h]
      · have hn : CounterPrograms.value (d.stacks 0) ≤ (d.stacks 1).length := by omega
        simp [h, hn]
    simpa [z, g, cleared] using hout
  · intro j hj2
    by_cases hj4 : j = 4
    · subst j; simp [z, g, cleared, hd 4 (by decide)]
    by_cases hj5 : j = 5
    · subst j; simp [z, cleared, hd 5 (by decide)]
    have hzf : z.stacks j = f.stacks j := by simp [z, g, cleared, hj4, hj5]
    rw [hzf, hff j hj2, hef j hj4 hj5, hcf j hj5]
    by_cases hj3 : j = 3
    · subst j; rw [hb3, hd 3 (by decide)]
    · exact (hbf j hj3 hj4).trans (haf j hj3)

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
