import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheRowCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeBoundedLoop

namespace OAI.Algorithms

/-! The actual outer unary loop produces every basis row exactly once. -/

namespace SubexponentialSAT.SubexpLagrangeCacheLoop

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheState
open SubexpLagrangeCachePreparation

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def encodeRows (rows : List (List (Coefficient p μ))) : List (List (List Bool)) :=
  rows.map (List.map SubexpFlatAdd.encode)

def Good (rows : List (List (Coefficient p μ))) (i : ℕ) : Prop :=
  List.Forall₂ (SubexpLagrangeCacheRowCorrectness.Correct p μ) rows (List.range i).reverse

def Invariant (x : Inputs) (zero one : Coefficient p μ) (i : ℕ) (d : Data) : Prop :=
  ∃ rows, Good p μ rows i ∧ d.stacks = SubexpLagrangeCacheOuterState.view p μ M
    (preparedStore x) zero one i (encodeRows p μ rows) (d.stacks 246)

theorem invariant_stable (x : Inputs) (zero one : Coefficient p μ) :
    UnaryForPrograms.FrameStable SubexpLagrangeCacheControl.outerCounter
      (Invariant p μ M x zero one) := by
  intro i a b hab hi
  obtain ⟨rows, hg, hs⟩ := hi
  refine ⟨rows, hg, ?_⟩
  funext k
  by_cases hk : k = 246
  · subst k
    simp [SubexpLagrangeCacheOuterState.view]
  · calc
      b.stacks k = a.stacks k := (hab k hk).symm
      _ = SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one i
          (encodeRows p μ rows) (a.stacks 246) k := congrFun hs k
      _ = SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one i
          (encodeRows p μ rows) (b.stacks 246) k := by
            simp [SubexpLagrangeCacheOuterState.view, hk]

theorem body_spec (hμ : 0 < μ) (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ))
    (H : SubexpLagrangeCacheContext.Valid p μ M x t zero one minusOne)
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hz : SubexpLagrangeInverseCall.denote p μ zero = 0)
    (ho : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1) (i : ℕ) (hi : i < p) (d : Data)
    (hd : Invariant p μ M x zero one i d) :
    ∃ n e, n ≤ SubexpLagrangeCacheRow.budget p (baseWidth p μ) i x.exponent x.precision ∧
      Eval (SubexpLagrangeCacheControl.outerStep SubexpLagrangeInverseCall.command) n d e ∧
      e.stacks SubexpLagrangeCacheControl.outerCounter.counter =
        d.stacks SubexpLagrangeCacheControl.outerCounter.counter ∧
      Invariant p μ M x zero one (i + 1) e := by
  obtain ⟨rows, hg, hs⟩ := hd
  let s := SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one i
    (encodeRows p μ rows) (d.stacks 246)
  have hdstate : d = (⟨d.regs, s⟩ : Data) :=
    congrArg (StructuredProgram.State.mk d.regs) hs
  have henv := SubexpLagrangeCacheInvariant.environment p μ M x t zero one minusOne H
    i (encodeRows p μ rows) (d.stacks 246)
  obtain ⟨n, rf, r, hn, he, hr⟩ := SubexpLagrangeCacheRowCorrectness.command_correct p μ M hμ
    t zero one minusOne x.width x.exponent x.precision s ⟨i, hi⟩ henv
    (encodeRows p μ rows) (by simp [s, SubexpLagrangeCacheOuterState.view])
    ht hz ho hm H.exponent H.precision d.regs
  let e : Data := ⟨rf, SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one
    (i + 1) (encodeRows p μ (r :: rows)) (d.stacks 246)⟩
  have hout : SubexpLagrangeCacheRow.output p μ M s zero one i
      (r.map SubexpFlatAdd.encode) (encodeRows p μ rows) = e.stacks :=
    SubexpLagrangeCacheInvariant.output_view p μ M (preparedStore x) zero one i
      (encodeRows p μ rows) (d.stacks 246) (r.map SubexpFlatAdd.encode)
  rw [hout, ← hdstate] at he
  have hgood : Good p μ (r :: rows) (i + 1) := by
    have h := List.Forall₂.cons hr hg
    simpa [Good, List.range_succ, List.reverse_append] using h
  refine ⟨n, e, hn, he, ?_, r :: rows, hgood, ?_⟩
  · simp [e, SubexpLagrangeCacheControl.outerCounter, SubexpLagrangeCacheOuterState.view]
  · simp [e, SubexpLagrangeCacheOuterState.view]

def loopBound (x : Inputs) (B : ℕ) : ℕ :=
  CounterForPrograms.budgetSum
    (fun i => SubexpLagrangeCacheRow.budget (primeValue x) B i x.exponent x.precision)
    0 (primeValue x) + 2 * primeValue x + 2

theorem loop_correct (hμ : 0 < μ) (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : Word (baseWidth p μ))
    (H : SubexpLagrangeCacheContext.Valid p μ M x t zero one minusOne)
    (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
    (hz : SubexpLagrangeInverseCall.denote p μ zero = 0)
    (ho : SubexpLagrangeInverseCall.denote p μ one = 1)
    (hm : wordValue p μ minusOne = -1) (regs : Fin 16 → Bool) :
    ∃ n rf rows, n ≤ loopBound x (baseWidth p μ) ∧
      Eval (SubexpLagrangeCacheControl.outerLoop SubexpLagrangeInverseCall.command) n
        (preparedState x regs)
        ⟨rf, SubexpLagrangeCacheOuterState.view p μ M (preparedStore x) zero one p
          (encodeRows p μ rows) []⟩ ∧ Good p μ rows p := by
  have hstart : Invariant p μ M x zero one 0 (preparedState x regs) := by
    refine ⟨[], List.Forall₂.nil, ?_⟩
    have hs := SubexpLagrangeCacheInvariant.initial_view p μ M x t zero one minusOne H
    simpa [preparedState, encodeRows, preparedStore, allocatedStore, unaryPrime, H.prime] using hs.symm
  obtain ⟨n, e, he, hi, hempty, hn⟩ := SubexpLagrangeBoundedLoop.for_correct
    SubexpLagrangeCacheControl.outerCounter
    (SubexpLagrangeCacheControl.outerStep SubexpLagrangeInverseCall.command)
    (Invariant p μ M x zero one)
    (fun i => SubexpLagrangeCacheRow.budget p (baseWidth p μ) i x.exponent x.precision) p
    (invariant_stable p μ M x zero one)
    (body_spec p μ M hμ x t zero one minusOne H ht hz ho hm)
    (preparedState x regs) (by
      simp [preparedState, preparedStore, SubexpLagrangeCacheControl.outerCounter,
        unaryPrime, H.prime]) hstart
  obtain ⟨rows, hg, hs⟩ := hi
  change e.stacks 246 = [] at hempty
  rw [hempty] at hs
  have hestate : e = (⟨e.regs, SubexpLagrangeCacheOuterState.view p μ M (preparedStore x)
      zero one p (encodeRows p μ rows) []⟩ : Data) :=
    congrArg (StructuredProgram.State.mk e.regs) hs
  rw [hestate] at he
  exact ⟨n, e.regs, rows, by simpa [loopBound, H.prime] using hn, he, hg⟩

end SubexponentialSAT.SubexpLagrangeCacheLoop

end OAI.Algorithms
