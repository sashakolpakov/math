import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramEmit
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramCombine
import OAI.Algorithms.SubexponentialSAT.SubexpInputFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 def state (regs : Fin 8 → Bool) (wi wh ci ch score source acc output : List Bool) : Data :=
  ⟨regs, ![wi,ci,wh,ch,score,[],[],[],source,acc,output,[]]⟩
 def ready (regs : Fin 8 → Bool) (wi wh source acc output : List Bool) :=
  state regs wi wh [] [] [] source acc output
 def weighted : Cmd 8 12 := liftCommand combineCommand 0 4 reg low
 def clear (j : Fin 12) : Cmd 8 12 := .call (SubexponentialSAT.StackRoutines.clearProgram j 0 1)


 def value (wi wh : List Bool) (p : ℕ × ℕ) :=
  SubexponentialSAT.CounterPrograms.value wi*p.1 + SubexponentialSAT.CounterPrograms.value wh*p.2
 def payload (p : ℕ × ℕ) : List Bool :=
  SubexponentialSAT.Encoding.frame (List.replicate p.1 false) ++
    SubexponentialSAT.Encoding.frame (List.replicate p.2 false)
 def pairBudget (wi wh : List Bool) (p : ℕ × ℕ) :=
  scaleBudget wi p.1 + scaleBudget wh p.2 + 8*(p.1+p.2) + 4*value wi wh p + 25

 def readFields : Cmd 8 12 :=
  .seq (SubexponentialSAT.SubexpInputFrames.readField 8 1 (by decide))
    (SubexponentialSAT.SubexpInputFrames.readField 8 3 (by decide))

 def pairCommand : Cmd 8 12 :=
  .seq readFields (.seq weighted (.seq (.seq (clear 1) (clear 3)) emit))

 theorem readFields_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (tail acc output : List Bool) :
    ∃ rf, Eval readFields (6*p.1+6*p.2+8)
      (ready regs wi wh (payload p ++ tail) acc output)
      (state rf wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output) := by
  let d := ready regs wi wh (payload p ++ tail) acc output
  let rest := SubexponentialSAT.Encoding.frame (List.replicate p.2 false) ++ tail
  obtain ⟨a, ha, hsa⟩ := SubexponentialSAT.SubexpInputFrames.readField_execute 8 1 (by decide) d
    (List.replicate p.1 false) rest (by simp [d, ready, state, payload, rest, List.append_assoc]) rfl
  have has : a.stacks = (state a.regs wi wh (List.replicate p.1 false) [] [] rest acc output).stacks := by
    rw [hsa]
    funext j; fin_cases j <;> simp [d,ready,state]
  obtain ⟨b, hb, hsb⟩ := SubexponentialSAT.SubexpInputFrames.readField_execute 8 3 (by decide) a
    (List.replicate p.2 false) tail (by rw [has]; rfl) (by rw [has]; rfl)
  have heb : b = state b.regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    rw [hsb,has]
    funext j; fin_cases j <;> simp [state]
  refine ⟨b.regs, ?_⟩
  have h := ha.seq hb
  rw [heb] at h
  convert h using 1 <;> simp only [readFields, List.length_replicate] ; omega

 theorem weighted_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (tail acc output : List Bool) :
    ∃ n ≤ scaleBudget wi p.1 + scaleBudget wh p.2 + 3, ∃ rf,
      Eval weighted n
        (state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output)
        (state rf wi wh (List.replicate p.1 false) (List.replicate p.2 false)
          (List.replicate (value wi wh p) false) tail acc output) := by
  let b := state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output
  obtain ⟨n, hn, c, hc, hco, hcf⟩ := combine_lifted reg low reg_injective low_injective b
    p.1 p.2 rfl rfl rfl rfl rfl
  have hec : c = state c.regs wi wh (List.replicate p.1 false) (List.replicate p.2 false)
      (List.replicate (value wi wh p) false) tail acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    funext j
    fin_cases j <;> first
      | simpa [low, b, state, value] using hco
      | exact (hcf _ (by decide)).trans (by rfl)
  refine ⟨n, ?_, c.regs, ?_⟩
  · simpa [combineBudget,projectState,reg,low,b,state] using hn
  · rw [hec] at hc
    exact hc

 theorem clearCounts_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (score tail acc output : List Bool) :
    ∃ rf, Eval (.seq (clear 1) (clear 3)) (2*p.1+2*p.2+6)
      (state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) score tail acc output)
      (state rf wi wh [] [] score tail acc output) := by
  let c := state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) score tail acc output
  let c₁ : Data := ⟨readRegs c.regs 0 1 none, Function.update c.stacks 1 []⟩
  let c₂ : Data := ⟨readRegs c₁.regs 0 1 none, Function.update c₁.stacks 3 []⟩
  have h1raw : Eval (clear 1) (2*(c.stacks 1).length+3) c c₁ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 1 0 1 c.regs c.stacks)
  have h2raw : Eval (clear 3) (2*(c₁.stacks 3).length+3) c₁ c₂ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 3 0 1 c₁.regs c₁.stacks)
  have hlen1 : (c.stacks 1).length=p.1 := by simp [c,state]
  have hlen2 : (c₁.stacks 3).length=p.2 := by simp [c₁,c,state]
  have h1 : Eval (clear 1) (2*p.1+3) c c₁ := by simpa only [hlen1] using h1raw
  have h2 : Eval (clear 3) (2*p.2+3) c₁ c₂ := by simpa only [hlen2] using h2raw
  have he : c₂ = state c₂.regs wi wh [] [] score tail acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    funext j; fin_cases j <;> rfl
  refine ⟨c₂.regs, ?_⟩
  have h := h1.seq h2
  rw [he] at h
  convert h using 1 ; omega

 theorem state_ready_of_frame (regs : Fin 8 → Bool) (wi wh score tail acc output : List Bool)
    (e : Data)
    (h4 : e.stacks 4=[])
    (h9 : e.stacks 9=CandidateScoreProgram.reverseRecord score acc)
    (hf : ∀ j,j≠4→j≠9→e.stacks j=(state regs wi wh [] [] score tail acc output).stacks j) :
    e=ready e.regs wi wh tail (CandidateScoreProgram.reverseRecord score acc) output := by
  apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj4 : j=4
  · subst j; exact h4
  by_cases hj9 : j=9
  · subst j; exact h9
  rw [hf j hj4 hj9]
  fin_cases j <;> simp_all [state,ready]

 theorem eval_congr_output {R S : ℕ} {cmd : Cmd R S} {n : ℕ}
    {a b c : State R S} (h : Eval cmd n a b) (he : b=c) : Eval cmd n a c := by
  cases he
  exact h

 theorem emit_ready_eval (regs : Fin 8 → Bool) (wi wh score tail acc output : List Bool) :
    ∃ rf, Eval emit (4*score.length+8)
      (state regs wi wh [] [] score tail acc output)
      (ready rf wi wh tail (CandidateScoreProgram.reverseRecord score acc) output) := by
  let d := state regs wi wh [] [] score tail acc output
  obtain ⟨e, he, he4, he9, hef⟩ := emit_eval d
  have hee : e = ready e.regs wi wh tail (CandidateScoreProgram.reverseRecord score acc) output :=
    state_ready_of_frame regs wi wh score tail acc output e he4 he9 hef
  exact ⟨e.regs,eval_congr_output he hee⟩

 theorem pairCommand_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (tail acc output : List Bool) :
    ∃ t ≤ pairBudget wi wh p, ∃ rf,
      Eval pairCommand t (ready regs wi wh (payload p ++ tail) acc output)
        (ready rf wi wh tail
          (CandidateScoreProgram.reverseRecord (List.replicate (value wi wh p) false) acc) output) := by
  obtain ⟨r₁,h₁⟩ := readFields_eval regs wi wh p tail acc output
  obtain ⟨n,hn,r₂,h₂⟩ := weighted_eval r₁ wi wh p tail acc output
  obtain ⟨r₃,h₃⟩ := clearCounts_eval r₂ wi wh p (List.replicate (value wi wh p) false) tail acc output
  obtain ⟨r₄,h₄⟩ := emit_ready_eval r₃ wi wh (List.replicate (value wi wh p) false) tail acc output
  refine ⟨_, ?_, r₄, h₁.seq (h₂.seq (h₃.seq h₄))⟩
  simp only [List.length_replicate]
  unfold pairBudget
  omega
end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
