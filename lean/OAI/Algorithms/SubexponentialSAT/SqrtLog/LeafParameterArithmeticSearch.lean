import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupSearch

namespace OAI.Algorithms

/-! Generic correctness for the actual tested square-times-coefficient search.
The command is exactly `Setup.Search.command`; there is no arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

open BitProgram StructuredCalls
open CounterPrograms (value)
open Setup.Search (Data guardPorts loopPorts body command iterationBound)

def root (coefficient bound : ℕ) : ℕ := Nat.sqrt (bound / coefficient)

theorem le_root_iff (coefficient bound a : ℕ) (hc : 0 < coefficient) :
    a ≤ root coefficient bound ↔ a^2 * coefficient ≤ bound := by
  rw [root, Nat.le_sqrt', Nat.le_div_iff_mul_le hc]

def Invariant (target : ℕ) (initial : Data) (i : ℕ) (d : Data) : Prop :=
  value (d.stacks 0) = i ∧ value (d.stacks 12) = min i target ∧
  (d.stacks 0).length ≤ i ∧ (d.stacks 12).length ≤ i ∧
  ∀ j : Fin 15, j ≠ 0 → j ≠ 12 → j ≠ 13 → j ≠ 14 →
    d.stacks j = initial.stacks j

theorem invariant_stable (target : ℕ) (initial : Data) :
    CounterForPrograms.FrameStable loopPorts (Invariant target initial) := by
  intro i a b hab hi
  rcases hi with ⟨hv,hs,hl,hl',hf⟩
  have hb0 := hab 0 (by decide) (by decide)
  have hb12 := hab 12 (by decide) (by decide)
  refine ⟨by simpa [← hb0] using hv, by simpa [← hb12] using hs,
    by simpa [← hb0] using hl, by simpa [← hb12] using hl', ?_⟩
  intro j h0 h12 h13 h14
  rw [← hab j h13 h14]
  exact hf j h0 h12 h13 h14

theorem body_spec (target : ℕ) (initial : Data)
    (htarget : ∀ a, a ≤ target ↔
      a^2 * value (initial.stacks 1) ≤ value (initial.stacks 2))
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → initial.stacks (guardPorts i) = []) :
    CounterForPrograms.BodySpec loopPorts body (Invariant target initial)
      (iterationBound initial) := by
  intro i d hi hscratch _
  rcases hi with ⟨hv,hs,hl,hl',hf⟩
  have hframe1 := hf 1 (by decide) (by decide) (by decide) (by decide)
  have hframe2 := hf 2 (by decide) (by decide) (by decide) (by decide)
  have hdempty : ∀ j : Fin 12, 3 ≤ j.val → d.stacks (guardPorts j) = [] := by
    intro j hj
    rw [hf (guardPorts j)]
    · exact hempty j hj
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 0 at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 12 at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 13 at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = 14 at hv
      omega
  obtain ⟨t,e,he,he0,he12,hef,ht⟩ := Setup.Search.body_eval d hdempty
  refine ⟨t,e,?_,he,hef 13 (by decide) (by decide),?_,?_⟩
  · dsimp [iterationBound]
    rw [hframe1,hframe2] at ht
    have harg : (d.stacks 0).length + (initial.stacks 1).length +
        (initial.stacks 2).length + (d.stacks 12).length + 2 ≤
        i + (initial.stacks 1).length + (initial.stacks 2).length + i + 2 := by omega
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  · exact (hef 14 (by decide) (by decide)).trans hscratch
  · refine ⟨by rw [he0,CounterPrograms.value_increment,hv],?_,?_,?_,?_⟩
    · rw [he12,hv,hframe1,hframe2]
      by_cases h : i+1 ≤ target
      · rw [ite_eq_left ((htarget (i+1)).1 h)]
        rw [CounterPrograms.value_increment,hv,Nat.min_eq_left h]
      · rw [ite_eq_right (fun hh => h ((htarget (i+1)).2 hh)),hs]
        omega
    · rw [he0]
      exact (CounterPrograms.ripple_length_le true (d.stacks 0)).trans (by omega)
    · rw [he12]
      split
      · exact (CounterPrograms.ripple_length_le true (d.stacks 0)).trans (by omega)
      · omega
    · intro j h0 h12 h13 h14
      exact (hef j h0 h12).trans (hf j h0 h12 h13 h14)

/-- Fully concrete arithmetic search: input 1 is a positive coefficient,
input 2 the bound, 13 the counted fuel. Every tested candidate is charged. -/
theorem command_eval (d : Data)
    (hc : 0 < value (d.stacks 1))
    (hfuel : root (value (d.stacks 1)) (value (d.stacks 2)) ≤ value (d.stacks 13))
    (hzero : d.stacks 0 = []) (hanswer : d.stacks 12 = [])
    (hscratch : d.stacks 14 = [])
    (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks (guardPorts i) = []) :
    ∃ t e, Eval command t d e ∧
      value (e.stacks 12) = root (value (d.stacks 1)) (value (d.stacks 2)) ∧
      (e.stacks 0).length ≤ value (d.stacks 13) ∧
      (e.stacks 12).length ≤ value (d.stacks 13) ∧
      (e.stacks 13).length = (d.stacks 13).length ∧ e.stacks 14 = [] ∧
      (∀ j : Fin 15, j ≠ 0 → j ≠ 12 → j ≠ 13 → j ≠ 14 → e.stacks j = d.stacks j) ∧
      t ≤ value (d.stacks 13) * iterationBound d (value (d.stacks 13)) +
        (value (d.stacks 13)+1) * (16*(d.stacks 13).length+16) := by
  let target := root (value (d.stacks 1)) (value (d.stacks 2))
  have hi : Invariant target d 0 d := by
    refine ⟨by simp [hzero],by simp [hanswer],
      by simp [hzero],by simp [hanswer],?_⟩
    intro j _ _ _ _; rfl
  obtain ⟨t,e,he,hei,_,hlen,hsc,ht⟩ := CounterForPrograms.for_correct loopPorts body
    (Invariant target d) (iterationBound d) (invariant_stable target d)
    (body_spec target d (fun a => le_root_iff _ _ a hc) hempty) d hscratch hi
  change Invariant target d (value (d.stacks 13)) e at hei
  change t ≤ CounterForPrograms.budgetSum (iterationBound d) 0 (value (d.stacks 13)) +
    (value (d.stacks 13)+1)*(16*(d.stacks 13).length+16) at ht
  rcases hei with ⟨_,hv,hl0,hl12,hframe⟩
  refine ⟨t,e,he,?_,hl0,hl12,hlen,hsc,hframe,?_⟩
  · dsimp [target] at hv
    simpa only [Nat.min_eq_right hfuel] using hv
  · apply ht.trans
    apply Nat.add_le_add_right
    apply CounterForPrograms.budgetSum_le
    intro i _ hil
    dsimp [iterationBound]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

end OAI.Algorithms
