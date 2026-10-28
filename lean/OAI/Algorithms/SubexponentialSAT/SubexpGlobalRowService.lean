import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowUniversal
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowConstants

namespace OAI.Algorithms

/-! All branches of the fixed global row program, at one actual incidence.
The output is computed from the physical packing, matrix recurrence and
cache words. No supplied row table or execution callback is an input. -/

namespace SubexponentialSAT.SubexpGlobalRowService

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpGlobalRowLookup SubexpGlobalRowSelection SubexpGlobalRowInputs
open Subexp.ConstructivePacking
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (contextStore)

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))

def outputAt (i : Fin Δ) (v w : Fin D) : Word :=
  match P.lookup v with
  | none => SubexpGlobalRowConstants.output μ source xs.length (decide (v.val = w.val))
  | some (block,u) =>
    match P.lookup w with
    | none => SubexpGlobalRowConstants.output μ source xs.length false
    | some (other,y) =>
      if block = other then SubexpGlobalRowValues.output source i u y xs inverse negative difference μ
      else SubexpGlobalRowConstants.output μ source xs.length false

noncomputable def costAt (scopes : List (List ℕ)) (e : ℕ) (a : Data)
    (i : Fin Δ) (v w : Fin D) : ℕ :=
  let V := SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType v
  let W := SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType w
  let b := SubexpLiftRing.baseWidth p 1
  match P.lookup v with
  | none => 400 * V^2 + 18 * v.val + 9 * w.val + 14 * (4 * b) +
      2 * P.leftovers.idxOf v + 99 +
      SubexpGlobalRowConstants.evaluationCost μ source xs.length (decide (v.val = w.val))
  | some (block,u) =>
    match P.lookup w with
    | none => 400 * V^2 + 400 * W^2 + 14 * (4 * b) +
        2 * (block.val + (Subexp.CollisionProgram.encodeType u).length + P.leftovers.idxOf w) + 75 +
        SubexpGlobalRowConstants.evaluationCost μ source xs.length false
    | some (other,y) =>
      if block = other then
        3 * (SubexpGlobalRowUniversal.classifyCost P scopes e v w block +
          SubexpGlobalRowUniversal.sourceCost xs inverse negative difference a i u y) + 52 + 16 +
          SubexpRowToTaylor.runtimeBound xs.length (baseWidth p 1) (baseWidth p μ)
            (SubexpRowToTaylorCalls.code
              (SubexpGlobalRowValues.expression source i u y xs inverse negative difference)).length
      else 400 * V^2 + 400 * W^2 + 18 * block.val + 9 * other.val + 14 * (4 * b) +
        2 * (block.val + (Subexp.CollisionProgram.encodeType u).length +
          other.val + (Subexp.CollisionProgram.encodeType y).length) + 101 +
        SubexpGlobalRowConstants.evaluationCost μ source xs.length false

theorem costAt_sameContext (scopes : List (List ℕ)) (e : ℕ) (a b : Data)
    (i : Fin Δ) (v w : Fin D) (h : SubexpDenseRowTableAssembly.SameContext a.stacks b.stacks) :
    costAt μ source xs inverse negative difference P scopes e b i v w =
      costAt μ source xs inverse negative difference P scopes e a i v w := by
  unfold costAt
  cases hv : P.lookup v with
  | none => rfl
  | some z =>
    rcases z with ⟨block,u⟩
    cases hw : P.lookup w with
    | none => rfl
    | some z =>
      rcases z with ⟨other,y⟩
      by_cases he : block = other
      · simp only [he, ite_eq_left, SubexpGlobalRowUniversal.sourceCost_sameContext
          xs inverse negative difference a b i u y h]
      · simp only [he, ite_false]

/-- Complete execution of the fixed row code on one actual typed incidence.
The only non-data hypotheses are primality, the nonzero-two condition and
the already-proved identification of the physical prefix slot. -/
theorem run_at (scopes : List (List ℕ)) (e : ℕ) (he : e ≤ scopes.length)
    (i : Fin Δ) (v w : Fin D)
    (hslot : SubexpIncidenceSlotProgram.degree scopes e v.val = i.val)
    (h2 : (2 : ZMod p) ≠ 0) (hμ : 0 < μ) (a : Data)
    (hm : Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hscopes : a.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (hfactor : a.stacks 261 = unary e)
    (hsource : a.stacks 260 = SubexpGlobalRowPacking.key v)
    (htarget : a.stacks 262 = SubexpGlobalRowPacking.key w) (ha : HighClean a)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one)
    (sw tw : Word) (frame : Fin 6 → Word) (context : Fin 252 → Word)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (xs.length + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (hf : ∀ j, a.stacks (SubexpRowToTaylorCalls.stack j) = contextStore context j) :
    ∃ n ≤ costAt μ source xs inverse negative difference P scopes e a i v w, ∃ regs,
      Eval SubexpGlobalRowUniversal.command n a
        (SubexpGlobalRowEvaluation.result a regs (outputAt μ source xs inverse negative difference P i v w)) := by
  have hzeroLength : (a.stacks 131).length = 4 * baseWidth p 1 := by
    rw [hzero, SubexpFlatAdd.encode_length]
  cases hv : P.lookup v with
  | none =>
    obtain ⟨n, hn, regs, hr⟩ := SubexpGlobalRowConstants.leftover μ source xs.length sw tw frame context
      Subexp.UniversalRowAssembly.callerCommand P Subexp.CollisionProgram.encodeType v w hv a
      htable hsource htarget ha hm.code hμ H hz h74 h87 hB hf hzero hone
    have hlen : (a.stacks (constantPort (decide (v.val = w.val)))).length = 4 * baseWidth p 1 := by
      rw [SubexpGlobalRowConstants.cached_coefficient source a hzero hone,
        SubexpFlatAdd.encode_length]
    refine ⟨n, ?_, regs, ?_⟩
    · simpa only [costAt, hv, hlen] using hn
    · simpa only [SubexpGlobalRowUniversal.command, outputAt, hv] using hr
  | some z =>
    rcases z with ⟨block,u⟩
    cases hw : P.lookup w with
    | none =>
      obtain ⟨n, hn, regs, hr⟩ := SubexpGlobalRowConstants.rightLeftover μ source xs.length sw tw frame context
        Subexp.UniversalRowAssembly.callerCommand P Subexp.CollisionProgram.encodeType v w block u hv hw a
        htable hsource htarget ha hm.code hμ H hz h74 h87 hB hf hzero hone
      refine ⟨n, ?_, regs, ?_⟩
      · simpa only [costAt, hv, hw, hzeroLength] using hn
      · simpa only [SubexpGlobalRowUniversal.command, outputAt, hv, hw] using hr
    | some z =>
      rcases z with ⟨other,y⟩
      by_cases heq : block = other
      · subst other
        obtain ⟨np, hnp, middleRegs, hp⟩ := SubexpGlobalRowUniversal.prepare_eval source xs inverse negative difference
          P scopes e he v w block i u y hv hw hslot h2 a hm htable hscopes hfactor hsource htarget ha hzero hone
        obtain ⟨n, hn, regs, hr⟩ := SubexpGlobalRowEvaluation.row_after_prepare p μ source xs.length
          sw tw frame context Subexp.UniversalRowAssembly.callerCommand hμ H hz h74 h87 hB
          (SubexpGlobalRowValues.expression source i u y xs inverse negative difference)
          a _ np hf hp rfl
        refine ⟨n, ?_, regs, ?_⟩
        · simp only [costAt, hv, hw]
          exact hn.trans (Nat.add_le_add_right (Nat.add_le_add_right hnp 16) _)
        · simpa only [SubexpGlobalRowUniversal.command, outputAt, hv, hw, ite_true,
            SubexpGlobalRowValues.output] using hr
      · obtain ⟨n, hn, regs, hr⟩ := SubexpGlobalRowConstants.differentBlock μ source xs.length sw tw frame context
          Subexp.UniversalRowAssembly.callerCommand P Subexp.CollisionProgram.encodeType v w block other u y
          heq hv hw a htable hsource htarget ha hm.code hμ H hz h74 h87 hB hf hzero hone
        refine ⟨n, ?_, regs, ?_⟩
        · simpa only [costAt, hv, hw, ite_eq_right heq, hzeroLength] using hn
        · simpa only [SubexpGlobalRowUniversal.command, outputAt, hv, hw, ite_eq_right heq] using hr

end SubexponentialSAT.SubexpGlobalRowService

end OAI.Algorithms
