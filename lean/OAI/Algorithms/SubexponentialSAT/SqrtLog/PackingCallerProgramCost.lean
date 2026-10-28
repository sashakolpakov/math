import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramOutput

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem stage_separated : ∀ p∈Wide.stagePairs,∀ q∈Wide.stagePairs,p.1≠q.2 := by
  intro p hp q hq h
  have hsrc : p.1.val < 417 ∨ 481 ≤ p.1.val := by
    simp only [Wide.stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  have hdst : 417 ≤ q.2.val ∧ q.2.val < 481 := by
    simp only [Wide.stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Wide.ports_val] <;> omega
  have := congrArg Fin.val h
  omega

theorem stageCost_le (a : Wide.Data) (B : ℕ) (h : WordBound B (Wide.project a)) :
    copyManyCost Wide.stagePairs (Wide.project a) ≤ 8*(7*B+5) :=
  copyManyCost_le Wide.stagePairs (Wide.project a) B stage_separated (fun p _hp=>h p.1)

theorem middle_wordBound (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (B : ℕ)
    (ha : WordBound B (Wide.project a)) (hb : WordBound B (bankOutput a p w tail)) :
    WordBound B (middle a p w tail) := by
  intro i
  by_cases hi : 417 ≤ i.val ∧ i.val < 481
  · simp only [middle]
    rw [dite_eq_left hi]
    exact hb ⟨i.val-417,by omega⟩
  · simp only [middle]
    rw [dite_eq_right hi]
    simpa only [Wide.project] using ha i

theorem budget_overhead_le (a : Wide.Data) (p : Problem) (he : Empty a)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (B : ℕ)
    (ha : WordBound B (Wide.project a)) (hb : WordBound B (bankOutput a p w tail)) :
    budget a p w tail ≤ coreBudget (Wide.parameterStore (Wide.project a)) p w tail+1100*(B+1) := by
  have hstage := stageCost_le a B ha
  have hfinish := Wide.finishCost_le (middle a p w tail) B
    (middle_wordBound a p w tail B ha hb)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.words)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.metadata)
    (by rw [middle_frame _ _ _ _ _ (by norm_num)]; exact he.plans)
    (middle_parked a p he w tail)
  unfold budget computeBudget
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
