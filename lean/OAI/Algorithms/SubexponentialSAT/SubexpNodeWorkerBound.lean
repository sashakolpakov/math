import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateIterationBound
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsCostBound
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceInputBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMomentCostBounds
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsPipeline
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWidePhase

namespace OAI.Algorithms

/-! Numeric substitution for the actual source/job/moment suffix.  The
source constructor is charged by its input theorem, and the interpreter is
charged by the serialized bytes of that same produced expression. -/

namespace SubexponentialSAT.SubexpNodeWorkerBound

open BitProgram SubexpMomentSourceProgram SubexpMomentSourceInputBounds
open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost SymbolicCost

abbrev Data := StructuredProgram.State 16 288
abbrev Bits := List Bool

def suffixSize (p : ℕ) (ctx : Context) (d : Data) : ℕ :=
  sizeParameter ctx + parameterSize ctx.dimension 4 (Nat.log 2 p + 1) +
  SubexpNodeJobsCostBound.scale ctx.dimension (indexBits ctx.dimension) +
  SubexpNodeJobsReady.contextSize ctx + (d.stacks 78).length + (d.stacks 116).length + 1

theorem suffixSize_pos (p : ℕ) (ctx : Context) (d : Data) : 1 ≤ suffixSize p ctx d := by
  unfold suffixSize
  omega

theorem inputBound_ge_length (ctx : Context) : ctx.template.length + 1 ≤ inputBound ctx := by
  have hS := sizeParameter_pos ctx
  have hT : 1 ≤ ctx.template.length + 1 := by omega
  have hT2 : ctx.template.length + 1 ≤ (ctx.template.length + 1)^2 :=
    Nat.le_self_pow (by decide) _
  have hscale : (ctx.template.length + 1)^2 ≤
      (sizeParameter ctx)^8 * (ctx.template.length + 1)^2 := by
    simpa only [one_mul] using Nat.mul_le_mul_right ((ctx.template.length + 1)^2)
      (Nat.one_le_pow 8 _ hS)
  unfold inputBound
  apply (hT2.trans hscale).trans
  simpa only [one_mul, Nat.mul_assoc] using
    Nat.mul_le_mul_right ((sizeParameter ctx)^8 * (ctx.template.length + 1)^2)
      (show 1 ≤ (1000000000000 : ℕ) by norm_num)

section Suffix

variable (p : ℕ) [Fact p.Prime] (ctx : Context)
  (M : SubexpPreparedQuartic.Modulus p (ctx.dimension + 1))
  (t z o : QuarticCode p ctx.dimension) (slots : List (RawIndex ctx.dimension))
  (inputs : List (BlockData ctx))
  (bytes : Bits → Bits)
  (expr : (Fin ctx.dimension → ℕ) → Algorithm.Expr (CoeffList ctx.dimension (QuarticCode p ctx.dimension)))

/-- This is the exact numeric expression returned by the source/job/moment
execution theorem, including its metadata copies and final cleanup. -/
def jobsPhaseCost (d : Data) : ℕ :=
  SubexpNodeJobsStage.masterBound bytes ctx.dimension (indexBits ctx.dimension)
    (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs)
    (SubexpNodeJobsPipeline.localState d) +
  9 * SubexpNodeJobsReady.contextSize ctx + 2 * ctx.template.length + 69 +
  SubexpConcreteMomentPhase.cost p ctx.dimension M t z o slots expr
    (SubexpQueryOrder.generatedQueries ctx.dimension) +
  SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState d) + 2

theorem jobsPhaseCost_le_input (d : Data)
    (htemplate : ctx.template = encodeTemplate (inputs.map BlockData.template))
    (hmaster : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords ctx.dimension))
    (hs : ∀ a ∈ slots, Retained ctx.dimension a)
    (hN : slots.length ≤ slotCount ctx.dimension)
    (hbytes : ∀ a : Fin ctx.dimension → ℕ, bytes (SubexpExponentController.momentWord a) =
      SubexpPostfixControl.serializeCode
        (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension) (expr a).compile)
    (hsize : ∀ a : Fin ctx.dimension → ℕ, (bytes (SubexpExponentController.momentWord a)).length ≤
      uniformSourceBytes ctx inputs) :
    jobsPhaseCost p ctx M t z o slots inputs bytes expr d ≤
      20000000000 * (suffixSize p ctx d)^14 * (monomialCount ctx.dimension)^5 * inputBound ctx := by
  let S := suffixSize p ctx d
  let J := inputBound ctx
  let X := monomialCount ctx.dimension
  let K := S^14 * X^5 * J
  have hS : 1 ≤ S := suffixSize_pos p ctx d
  have hJ : 1 ≤ J := (show 1 ≤ ctx.template.length + 1 by omega).trans (inputBound_ge_length ctx)
  have hX : 1 ≤ X := Nat.choose_pos (by omega)
  have hS14 : 1 ≤ S^14 := Nat.one_le_pow 14 S hS
  have hX5 : 1 ≤ X^5 := Nat.one_le_pow 5 X hX
  have hK : 1 ≤ K := Nat.mul_le_mul (Nat.mul_le_mul hS14 hX5) hJ
  have hJK : J ≤ K := by
    simpa only [one_mul] using Nat.mul_le_mul_right J (Nat.mul_le_mul hS14 hX5)
  have hSK : S ≤ K := by
    calc
      S = S * 1 * 1 := by omega
      _ ≤ S^14 * X^5 * J := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.le_self_pow (by decide) S) hX5) hJ
  have htime := uniformTotalBudget_le_input ctx inputs htemplate
  have hlength := uniformSourceBytes_le_input ctx inputs htemplate
  have hTU : uniformTotalBudget ctx inputs + 8 + uniformSourceBytes ctx inputs + 1 ≤ 11 * J := by
    change uniformTotalBudget ctx inputs ≤ J at htime
    change uniformSourceBytes ctx inputs ≤ J at hlength
    omega
  have hjob := SubexpNodeJobsCostBound.masterBound_le bytes ctx.dimension (indexBits ctx.dimension)
    (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs)
    (SubexpNodeJobsPipeline.localState d) hmaster (by
      intro bits hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact hsize a)
  have hjobS : SubexpNodeJobsCostBound.scale ctx.dimension (indexBits ctx.dimension) ≤ S := by
    dsimp [S, suffixSize]
    omega
  have hjobpower : (SubexpNodeJobsCostBound.scale ctx.dimension (indexBits ctx.dimension))^3 ≤ S^14 :=
    (Nat.pow_le_pow_left hjobS 3).trans (Nat.pow_le_pow_right hS (by decide))
  have hXpow : X ≤ X^5 := Nat.le_self_pow (by decide) X
  have hjobK : SubexpNodeJobsStage.masterBound bytes ctx.dimension (indexBits ctx.dimension)
      (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs)
      (SubexpNodeJobsPipeline.localState d) ≤ 13200 * K := by
    apply hjob.trans
    change 1200 * (SubexpNodeJobsCostBound.scale ctx.dimension (indexBits ctx.dimension))^3 *
      (uniformTotalBudget ctx inputs + 8 + uniformSourceBytes ctx inputs + 1) * X ≤ _
    calc
      _ ≤ 1200 * S^14 * (11 * J) * X^5 := by gcongr
      _ = _ := by dsimp [K]; ring
  have hphase := SubexpMomentCostBounds.generated_cost_le p ctx.dimension M t z o slots expr hs hN
    (uniformSourceBytes ctx inputs) (by
      intro q hq
      unfold SubexpMomentCostBounds.sourceBytes
      rw [← hbytes q.exponent]
      exact hsize q.exponent)
  have hphaseS : parameterSize ctx.dimension 4 (Nat.log 2 p + 1) ≤ S := by
    dsimp [S, suffixSize]
    omega
  have hlength1 : uniformSourceBytes ctx inputs + 1 ≤ 2 * J := by
    change uniformSourceBytes ctx inputs ≤ J at hlength
    omega
  have hphaseK : SubexpConcreteMomentPhase.cost p ctx.dimension M t z o slots expr
      (SubexpQueryOrder.generatedQueries ctx.dimension) ≤ 10000000000 * K := by
    apply hphase.trans
    calc
      _ ≤ 5000000000 * S^14 * X^5 * (2 * J) := by gcongr
      _ = _ := by dsimp [K]; ring
  have hctx : SubexpNodeJobsReady.contextSize ctx ≤ S := by dsimp [S, suffixSize]; omega
  have h78 : (d.stacks 78).length ≤ S := by dsimp [S, suffixSize]; omega
  have h116 : (d.stacks 116).length ≤ S := by dsimp [S, suffixSize]; omega
  have htemplateJ : ctx.template.length ≤ J := (Nat.le_succ _).trans (inputBound_ge_length ctx)
  have hclear : SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState d) ≤ 4 * S + 6 := by
    change 2 * (d.stacks 78).length + 2 * (d.stacks 116).length + 6 ≤ _
    omega
  unfold jobsPhaseCost
  change _ ≤ 20000000000 * S^14 * X^5 * J
  have hfinal : SubexpNodeJobsStage.masterBound bytes ctx.dimension (indexBits ctx.dimension)
      (uniformTotalBudget ctx inputs + 8) (uniformSourceBytes ctx inputs)
      (SubexpNodeJobsPipeline.localState d) +
      9 * SubexpNodeJobsReady.contextSize ctx + 2 * ctx.template.length + 69 +
      SubexpConcreteMomentPhase.cost p ctx.dimension M t z o slots expr
        (SubexpQueryOrder.generatedQueries ctx.dimension) +
      SubexpNodePhaseExecution.clearCost (SubexpNodeWidePhase.localState d) + 2 ≤ 20000000000 * K := by
    omega
  simpa only [K, Nat.mul_assoc] using hfinal

end Suffix

end SubexponentialSAT.SubexpNodeWorkerBound

end OAI.Algorithms
