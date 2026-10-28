import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientStaging
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram

namespace OAI.Algorithms

/-! Actual normalization and unary conversion before coefficient search. -/

namespace SubexponentialSAT.SubexpCoefficientInputs

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupBoundSpec
open SubexpCoefficientStaging

private abbrev tiny {l : ℕ} (p : Program 3 3 l) (out : Fin 3)
    (src dst : Fin 64) (hs : 32 ≤ src.val ∧ src.val < 63)
    (hd : 32 ≤ dst.val ∧ dst.val < 63) : Stage where
  registers := 3
  stackCount := 3
  labels := l
  program := p
  register_le := by decide
  stack_le := by decide
  inputs := [(src, 0)]
  inputs_length := by simp
  inputs_nodup := by simp
  source_high := by intro q hq; obtain rfl := List.mem_singleton.mp hq; exact hs
  target_low := by
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    change (0 : ℕ) < 3
    decide
  output := out
  destination := dst
  destination_high := hd

def normalize : Stage := tiny CounterNormalizeProgram.program 0 40 45 (by decide) (by decide)
def radius : Stage := tiny CounterConversions.unaryProgram 1 43 46 (by decide) (by decide)
def start : Stage := tiny CounterConversions.unaryProgram 1 44 47 (by decide) (by decide)

private theorem tiny_project {l : ℕ} (p : Program 3 3 l) (out : Fin 3)
    (src dst : Fin 64) (hs : 32 ≤ src.val ∧ src.val < 63)
    (hd : 32 ≤ dst.val ∧ dst.val < 63) (a : Data) :
    let s := tiny p out src dst hs hd
    project s.register s.stack (s.prepared a) =
      CounterConversions.state ((s.prepared a).regs ∘ s.register) (a.stacks src) [] := by
  dsimp only
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · have hsrc0 : src ≠ (0 : Fin 64) := by
      intro h
      have hv := congrArg (fun x : Fin 64 => x.val) h
      norm_num at hv
      omega
    have hsrc63 : src ≠ (63 : Fin 64) := by
      intro h
      have hv := congrArg (fun x : Fin 64 => x.val) h
      norm_num at hv
      omega
    have hsrc1 : src ≠ (1 : Fin 64) := by
      intro h
      have hv := congrArg (fun x : Fin 64 => x.val) h
      norm_num at hv
      omega
    have hsrc2 : src ≠ (2 : Fin 64) := by
      intro h
      have hv := congrArg (fun x : Fin 64 => x.val) h
      norm_num at hv
      omega
    have hsrcWork : src ∉ (tiny p out src dst hs hd).work := by
      rw [Stage.mem_work]
      change ¬ src.val < 3
      omega
    funext i
    fin_cases i <;>
      simp [Stage.prepared, prepareState, beforeCopies, resetMany_stacks,
        clearMany_stacks, copyManyState, copyState_stack, tiny, Stage.stack,
        Stage.work, hsrc0, hsrc1, hsrc2, hsrc63]

theorem normalize_run (p B : ℕ) (a : Data) (ha : WordBound B a)
    (hp : CounterPrograms.value (a.stacks 40) = p) (hpos : 0 < p) :
    ∃ t b, Eval normalize.command t a b ∧
      t ≤ 400 * (B + (9 * B + 21) + 1) ∧ WordBound (B + (9 * B + 21)) b ∧
      b.stacks 45 = SubexpAlphabetProgram.primeWord p ∧
      (∀ i : Fin 64, 32 ≤ i.val → i ≠ 63 → i ≠ 45 → b.stacks i = a.stacks i) := by
  let s := normalize
  let regs := (s.prepared a).regs ∘ s.register
  let out := CounterNormalizeProgram.state CounterNormalizeProgram.zeroRegs
    (SubexpAlphabetProgram.primeWord p) []
  have hr := CounterNormalizeProgram.normalize_runs regs (a.stacks 40) (hp.symm ▸ hpos)
  have hword : SubexpLiftRing.fixedBits (Nat.log2 (CounterPrograms.value (a.stacks 40)) + 1)
      (CounterPrograms.value (a.stacks 40)) = SubexpAlphabetProgram.primeWord p := by
    simp only [hp, Nat.log2_eq_log_two, SubexpAlphabetProgram.primeWord,
      SubexpEnumerationPayload.scalarWidth]
  rw [hword] at hr
  have hin := tiny_project CounterNormalizeProgram.program 0 40 45 (by decide) (by decide) a
  change project s.register s.stack (s.prepared a) =
    CounterNormalizeProgram.state regs (a.stacks 40) [] at hin
  have hrun : RunsIn s.program (9 * B + 21)
      ((project s.register s.stack (s.prepared a)).withPC (some s.program.entry))
      (out.withPC none) := by
    rw [hin]
    obtain ⟨t, ht, he⟩ := hr
    exact ⟨t, ht.trans (by have := ha 40; omega), he⟩
  obtain ⟨t, he, ht, hw⟩ := s.run a out B (9 * B + 21) ha hrun
  exact ⟨t, s.result a out, he, ht, hw, s.result_output a out,
    fun i hi h63 h45 => s.result_frame a out i hi h63 h45⟩

private theorem unary_run (src dst : Fin 64)
    (hs : 32 ≤ src.val ∧ src.val < 63) (hd : 32 ≤ dst.val ∧ dst.val < 63)
    (N L B : ℕ) (a : Data) (ha : WordBound B a)
    (hv : CounterPrograms.value (a.stacks src) = N) (hl : (a.stacks src).length ≤ L) :
    let s := tiny CounterConversions.unaryProgram 1 src dst hs hd
    ∃ t b, Eval s.command t a b ∧
      t ≤ 400 * (B + 32 * (N + 1) * (L + 1) + 1) ∧
      WordBound (B + 32 * (N + 1) * (L + 1)) b ∧
      b.stacks dst = List.replicate N true ∧
      (∀ i : Fin 64, 32 ≤ i.val → i ≠ 63 → i ≠ dst → b.stacks i = a.stacks i) := by
  dsimp only
  let s := tiny CounterConversions.unaryProgram 1 src dst hs hd
  let regs := (s.prepared a).regs ∘ s.register
  let out := CounterConversions.state CounterConversions.zeroRegs [] (List.replicate N true)
  have hr := CounterConversions.unary_runs regs (a.stacks src) []
  simp only [hv, List.append_nil] at hr
  have hin := tiny_project CounterConversions.unaryProgram 1 src dst hs hd a
  have hrun : RunsIn s.program (32 * (N + 1) * (L + 1))
      ((project s.register s.stack (s.prepared a)).withPC (some s.program.entry))
      (out.withPC none) := by
    rw [hin]
    obtain ⟨t, ht, he⟩ := hr
    refine ⟨t, ht.trans ?_, he⟩
    simp only [CounterConversions.runtimeBound, hv]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hl 1)
  obtain ⟨t, he, ht, hw⟩ := s.run a out B (32 * (N + 1) * (L + 1)) ha hrun
  exact ⟨t, s.result a out, he, ht, hw, s.result_output a out,
    fun i hi h63 hdst => s.result_frame a out i hi h63 hdst⟩

def command : Code := .seq normalize.command (.seq radius.command start.command)
def innerBound (B A R : ℕ) : ℕ := 9 * B + 21 +
  32 * (R + 1) * (B + 1) + 32 * (A + 1) * (B + 1)
def budget (B A R : ℕ) : ℕ := 1200 * (B + innerBound B A R + 1)

theorem command_run (p A R B : ℕ) (a : Data) (ha : WordBound B a)
    (hp : CounterPrograms.value (a.stacks 40) = p) (hpos : 0 < p)
    (hr : CounterPrograms.value (a.stacks 43) = R)
    (hA : CounterPrograms.value (a.stacks 44) = A) :
    ∃ t b, Eval command t a b ∧ t ≤ budget B A R ∧
      WordBound (B + innerBound B A R) b ∧
      b.stacks 45 = SubexpAlphabetProgram.primeWord p ∧
      b.stacks 46 = List.replicate R true ∧ b.stacks 47 = List.replicate A true ∧
      (∀ i : Fin 64, 32 ≤ i.val → i ≠ 63 → i ≠ 45 → i ≠ 46 → i ≠ 47 →
        b.stacks i = a.stacks i) := by
  obtain ⟨tn, n, en, htn, hwn, hn45, hnf⟩ := normalize_run p B a ha hp hpos
  have hn43 := hnf 43 (by decide) (by decide) (by decide)
  have hn44 := hnf 44 (by decide) (by decide) (by decide)
  obtain ⟨tr, r, er, htr, hwr, hr46, hrf⟩ := unary_run 43 46 (by decide) (by decide)
    R B (B + (9 * B + 21)) n hwn (by simpa only [hn43] using hr)
      (by rw [hn43]; exact ha 43)
  have hr44 := hrf 44 (by decide) (by decide) (by decide)
  obtain ⟨tA, b, eA, htA, hwb, hb47, hbf⟩ := unary_run 44 47 (by decide) (by decide)
    A B (B + (9 * B + 21) + 32 * (R + 1) * (B + 1)) r hwr
      (by simpa only [hr44, hn44] using hA) (by rw [hr44, hn44]; exact ha 44)
  refine ⟨tn + (tr + tA), b, en.seq (er.seq eA), ?_, ?_, ?_, ?_, hb47, ?_⟩
  · unfold budget innerBound
    omega
  · simpa only [innerBound, Nat.add_assoc] using hwb
  · exact (hbf 45 (by decide) (by decide) (by decide)).trans
      ((hrf 45 (by decide) (by decide) (by decide)).trans hn45)
  · exact (hbf 46 (by decide) (by decide) (by decide)).trans hr46
  · intro i hi h63 h45 h46 h47
    exact (hbf i hi h63 h47).trans ((hrf i hi h63 h46).trans (hnf i hi h63 h45))

end SubexponentialSAT.SubexpCoefficientInputs

end OAI.Algorithms
