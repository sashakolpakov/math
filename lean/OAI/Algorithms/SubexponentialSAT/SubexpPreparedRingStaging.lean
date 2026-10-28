import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuarticSetup
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedRingStagingCore
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# Physical staging of both prepared rings

This is one fixed 16-register, 51-stack program. Stacks 0..35 are owned
staging space, 36..38 hold retained prime/precision/coefficient inputs,
39..44 hold the target ring, and 45..50 hold the source ring. The source
precision word `[true]` is produced by real instructions. Both calls use
the same finite prepared-ring setup program; no cache is supplied by an
execution premise.

The Main adapter maps only these stacks, so its size bound does not include
an unread leaf stream or the protected threshold bank.
-/

namespace SubexponentialSAT.SubexpPreparedRingStaging

open BitProgram StructuredCalls SubexpSetupStorage
open SubexpPreparedSetupCalls (StackBound)
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing

def stage (source : Bool) : Command :=
  stageWith SubexpPreparedQuarticSetup.program source

theorem prepared_eq (source : Bool) (a : Data) (p : ℕ)
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : a.stacks 38 = SubexpPreparedQuarticSetup.flat coeff) :
    project id calleePort (prepared source a) =
      SubexpPreparedQuarticSetup.initialState p (a.stacks 36)
        (a.stacks (precisionPort source)) coeff := by
  simpa only [inputState, SubexpPreparedQuarticSetup.initialState, hc] using
    prepared_eq_words source a

theorem stage_eval (source : Bool) (a : Data) (out : SubexpPreparedSetupCalls.Data)
    {t : ℕ}
    (ht : Trace SubexpPreparedQuarticSetup.program t
      ((project id calleePort (prepared source a)).withPC
        (some SubexpPreparedQuarticSetup.program.entry)) (out.withPC none)) :
    Eval (stage source) (stageCost source a out t) a (returned source a out) :=
  stageWith_eval SubexpPreparedQuarticSetup.program source a out ht

def bankWords (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    Fin 6 → List Bool :=
  let prepared := SubexpPreparedQuarticSetup.preparedData p D coeff hc
  ![prepared.modulus.bits, SubexpPreparedQuarticPrelude.widthWord p (D + 1),
    SubexpPreparedQuarticSetup.flat prepared.reduction,
    SubexpPreparedQuarticSetup.flat prepared.zero,
    SubexpPreparedQuarticSetup.flat prepared.one,
    (SubexpPreparedQuarticSetup.minusOne p (D + 1)).val]

/-- The zero cache has canonical all-false bytes. -/
theorem bankWords_zero (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    bankWords p D coeff hc 3 = List.replicate (4 * baseWidth p (D + 1)) false := by
  change SubexpPreparedQuarticSetup.flat (SubexpPreparedQuartic.prepareZero p (D + 1)).1 = _
  rw [← SubexpPreparedQuarticSetup.literalZero_eq_source p (D + 1) (Nat.zero_lt_succ _)]
  change fixedBits (baseWidth p (D + 1)) 0 ++
    List.replicate (3 * baseWidth p (D + 1)) false = _
  rw [SubexpPreparedQuarticSetup.fixedBits_zero, ← List.replicate_add]
  congr 1
  omega

def HasBank (a : Data) (source : Bool) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) : Prop :=
  ∀ i, a.stacks (destination source i) = bankWords p D coeff hc i

def localBudget (p D : ℕ) (prime precision : List Bool) : ℕ :=
  SubexpPreparedQuarticSetup.runtimeBound p (D + 1)
    (SubexpPreparedQuarticSetup.storageBound p (D + 1) prime precision) prime precision

theorem stage_run (source : Bool) (a : Data) (p D W : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (ha : StackBound a W) (hp : BinaryArithmetic.toNat (a.stacks 36) = p)
    (he : BinaryArithmetic.toNat (a.stacks (precisionPort source)) = D + 1)
    (hcoeff : a.stacks 38 = SubexpPreparedQuarticSetup.flat coeff)
    (hW : SubexpPreparedQuarticSetup.storageBound p (D + 1)
      (a.stacks 36) (a.stacks (precisionPort source)) ≤ W) :
    ∃ n b, Eval (stage source) n a b ∧
      n ≤ localBudget p D (a.stacks 36) (a.stacks (precisionPort source)) + 400 * (W + 1) ∧
      StackBound b W ∧ HasBank b source p D coeff hc ∧
      (∀ i : Fin 51, 34 < i.val → (∀ j, i ≠ destination source j) → b.stacks i = a.stacks i) := by
  obtain ⟨out, ht, hbound, hcache, _, _⟩ :=
    SubexpPreparedQuarticSetup.run_prepared_bounded p D (a.stacks 36)
      (a.stacks (precisionPort source)) coeff hp he hc
  obtain ⟨t, htle, htrace⟩ := ht
  have hbo : StackBound out W := fun i => (hbound i).trans hW
  refine ⟨stageCost source a out t, returned source a out,
    stage_eval source a out ?_, ?_, returned_bound source a out ha hbo, ?_,
    returned_frame source a out⟩
  · rw [prepared_eq source a p coeff hcoeff]
    exact htrace
  · exact (stageCost_le source a out t W ha hbo).trans (Nat.add_le_add_right htle _)
  · intro i
    rw [returned_word]
    have heq : calleeOutput i = SubexpPreparedSetupCalls.cache ⟨3 + i.val, by omega⟩ := by
      apply Fin.ext
      simp [calleeOutput, SubexpPreparedSetupCalls.cache]
      omega
    rw [heq]
    have h := congrFun hcache ⟨3 + i.val, by omega⟩
    fin_cases i <;> simpa [SubexpPreparedSetupCalls.cacheWords, bankWords] using h

def command : Command := .seq (stage false) (.seq literalCommand (.seq (stage true) cleanup))
abbrev program : Program 16 51 (size command + 1) := compiled command 36 41

structure Result (a b : Data) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) : Prop where
  target : HasBank b false p D coeff hc
  source : HasBank b true p 0 coeff hc
  inputs : ∀ i, b.stacks (inputPort i) = a.stacks (inputPort i)
  scratch : ∀ i : Fin 36, b.stacks (i.castAdd 15) = []
  registers : ∀ i, b.regs i = false

def runtimeBound (p D W : ℕ) (prime precision : List Bool) : ℕ :=
  localBudget p D prime precision + localBudget p 0 prime [true] + 1000 * (W + 1)

theorem command_run (a : Data) (p D W : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (ha : StackBound a W) (hp : BinaryArithmetic.toNat (a.stacks 36) = p)
    (he : BinaryArithmetic.toNat (a.stacks 37) = D + 1)
    (hcoeff : a.stacks 38 = SubexpPreparedQuarticSetup.flat coeff)
    (hW : 1 ≤ W)
    (htarget : SubexpPreparedQuarticSetup.storageBound p (D + 1)
      (a.stacks 36) (a.stacks 37) ≤ W)
    (hsource : SubexpPreparedQuarticSetup.storageBound p 1 (a.stacks 36) [true] ≤ W) :
    ∃ n b, Eval command n a b ∧
      n + 1 ≤ runtimeBound p D W (a.stacks 36) (a.stacks 37) ∧
      StackBound b W ∧ Result a b p D coeff hc := by
  obtain ⟨nt, bt, ht, hnt, hbt, htargetBank, htf⟩ :=
    stage_run false a p D W coeff hc ha hp he hcoeff htarget
  have tf (i : Fin 51) (hi : 35 ≤ i.val) (hj : i.val < 39) : bt.stacks i = a.stacks i := by
    apply htf i (by omega)
    intro j h
    have hv := congrArg (fun k : Fin 51 => k.val) h
    simp only [destination, Bool.false_eq_true, ↓reduceIte] at hv
    omega
  let bl := literalState bt
  have hl := literal_eval bt
  have hbl : StackBound bl W := literal_bound bt hbt hW
  have h36 : bl.stacks 36 = a.stacks 36 :=
    (literal_frame bt 36 (by decide)).trans (tf 36 (by decide) (by decide))
  have h38 : bl.stacks 38 = a.stacks 38 :=
    (literal_frame bt 38 (by decide)).trans (tf 38 (by decide) (by decide))
  have h35 : bl.stacks (precisionPort true) = [true] := by simp [bl, literalState, precisionPort]
  obtain ⟨ns, bs, hs, hns, hbs, hsourceBank, hsf⟩ :=
    stage_run true bl p 0 W coeff hc hbl (by rw [h36]; exact hp)
      (by rw [h35]; rfl) (h38.trans hcoeff) (by rw [h36, h35]; exact hsource)
  have hclean := cleanup_eval bs
  have hbound := SubexpPreparedSetupCalls.clearManyCost_le scratchPorts bs hbs
  have hlen : scratchPorts.length = 36 := by simp [scratchPorts]
  rw [hlen] at hbound
  have hbit := hbt literalPort
  refine ⟨nt + ((2 * (bt.stacks literalPort).length + 5) +
    (ns + (clearManyCost scratchPorts bs + 16))), cleaned bs,
    .seq ht (.seq hl (.seq hs hclean)), ?_, ?_, ?_⟩
  · simp only [precisionPort, Bool.false_eq_true, ↓reduceIte] at hnt
    rw [h36, h35] at hns
    unfold runtimeBound
    omega
  · exact SubexpPreparedSetupCalls.clearMany_bound scratchPorts bs hbs
  · constructor
    · intro i
      rw [cleaned_frame bs _ (by simp [destination]; omega)]
      rw [hsf _ (by simp [destination]; omega) (by
        intro j h
        have hv := congrArg (fun k : Fin 51 => k.val) h
        simp only [destination, Bool.false_eq_true, ↓reduceIte] at hv
        omega)]
      rw [literal_frame bt _ (by
        intro h
        have hv := congrArg (fun k : Fin 51 => k.val) h
        simp [destination, literalPort] at hv
        omega)]
      exact htargetBank i
    · intro i
      rw [cleaned_frame bs _ (by simp [destination]; omega)]
      exact hsourceBank i
    · intro i
      rw [cleaned_frame bs _ (by simp only [inputPort]; omega)]
      rw [hsf _ (by simp only [inputPort]; omega) (by
        intro j h
        have hv := congrArg (fun k : Fin 51 => k.val) h
        simp only [inputPort, destination, ↓reduceIte] at hv
        omega)]
      rw [literal_frame bt _ (by
        intro h
        have hv := congrArg (fun k : Fin 51 => k.val) h
        simp only [inputPort, literalPort] at hv
        omega)]
      exact tf _ (by simp only [inputPort]; omega) (by simp only [inputPort]; omega)
    · intro i
      change (clearManyState scratchPorts bs).stacks _ = []
      rw [clearMany_stacks, ite_eq_left]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · intro i
      rfl

theorem program_runsIn (a : Data) (p D W : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (ha : StackBound a W) (hp : BinaryArithmetic.toNat (a.stacks 36) = p)
    (he : BinaryArithmetic.toNat (a.stacks 37) = D + 1)
    (hcoeff : a.stacks 38 = SubexpPreparedQuarticSetup.flat coeff)
    (hW : 1 ≤ W)
    (htarget : SubexpPreparedQuarticSetup.storageBound p (D + 1)
      (a.stacks 36) (a.stacks 37) ≤ W)
    (hsource : SubexpPreparedQuarticSetup.storageBound p 1 (a.stacks 36) [true] ≤ W) :
    ∃ b, RunsIn program (runtimeBound p D W (a.stacks 36) (a.stacks 37))
      (a.withPC (some program.entry)) (b.withPC none) ∧
      StackBound b W ∧ Result a b p D coeff hc := by
  obtain ⟨n, b, hn, hb, hw, hr⟩ := command_run a p D W coeff hc ha hp he hcoeff hW htarget hsource
  exact ⟨b, ⟨n + 1, hb, compiled_halt_trace hn 36 41⟩, hw, hr⟩

/-- A bound computed from the actual selected input storage and the sizes of
the two computed rings. It contains no unselected caller stack. -/
def wordBound (a : Data) (p D : ℕ) : ℕ :=
  stackBits a.stacks +
    SubexpPreparedQuarticSetup.storageBound p (D + 1) (a.stacks 36) (a.stacks 37) +
    SubexpPreparedQuarticSetup.storageBound p 1 (a.stacks 36) [true] + 1

theorem input_wordBound (a : Data) (p D : ℕ) : StackBound a (wordBound a p D) := by
  intro i
  have hi : (a.stacks i).length ≤ stackBits a.stacks := by
    unfold stackBits
    exact Finset.single_le_sum (f := fun j : Fin 51 => (a.stacks j).length)
      (s := Finset.univ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold wordBound
  omega

theorem run (a : Data) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : BinaryArithmetic.toNat (a.stacks 36) = p) (he : BinaryArithmetic.toNat (a.stacks 37) = D + 1)
    (hcoeff : a.stacks 38 = SubexpPreparedQuarticSetup.flat coeff) :
    ∃ b, RunsIn program (runtimeBound p D (wordBound a p D) (a.stacks 36) (a.stacks 37))
      (a.withPC (some program.entry)) (b.withPC none) ∧
      StackBound b (wordBound a p D) ∧ Result a b p D coeff hc := by
  apply program_runsIn a p D (wordBound a p D) coeff hc (input_wordBound a p D)
    hp he hcoeff
  all_goals unfold wordBound; omega

end SubexponentialSAT.SubexpPreparedRingStaging

end OAI.Algorithms
