import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerBound

namespace OAI.Algorithms

/-! The actual prepared-template bytes and source input bound yield the
eighth power of the same enumeration count in the complete job/phase
suffix. No source-size or overall-runtime certificate is postulated. -/

namespace SubexponentialSAT.SubexpNodeWorkerIterationBound

open Subexp.ConstructivePacking SubexpNodeBankBounds SubexpNodeTemplateIterationBound
open SubexpNodeWorkerBound SubexpMomentSourceInputBounds
open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost SymbolicCost
open SubexpSelectedConversions

private theorem source_arithmetic (A B S J N : ℕ)
    (hB : 1 ≤ B) (hJ : 1 ≤ J) (hAS : A ≤ S) (hBS : B ≤ S)
    (hN : N ≤ 10^27 * B^13 * J^4) :
    10^12 * A^8 * (N+1)^2 ≤ 10^67 * S^34 * J^8 := by
  have hpos : 1 ≤ B^13 * J^4 :=
    Nat.mul_le_mul (Nat.one_le_pow 13 B hB) (Nat.one_le_pow 4 J hJ)
  have hN1 : N+1 ≤ 2 * 10^27 * B^13 * J^4 := by nlinarith only [hN, hpos]
  have hN2 : N+1 ≤ 2 * 10^27 * S^13 * J^4 := by
    apply hN1.trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBS 13))
  calc
    _ ≤ 10^12 * S^8 * (2 * 10^27 * S^13 * J^4)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hAS 8))
        (Nat.pow_le_pow_left hN2 2)
    _ = (4 * 10^66) * (S^34 * J^8) := by ring
    _ ≤ 10^67 * S^34 * J^8 := by
      have h : 4 * 10^66 ≤ (10^67 : ℕ) := by norm_num
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (S^34 * J^8) h

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {t : Fin c.Q}

def scale {Q : ℕ}
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : List Bool)
    (store : SubexpRawTemplate.Store) (q : ℕ)
    (ctx : SubexpMomentSourceProgram.Context) (d : SubexpNodeWorkerBound.Data) : ℕ :=
  preparedSize (p := p) packing items suffix store q + suffixSize p ctx d

theorem inputBound_le_iterations (e : SubexpLayoutSpec.EnumerationData L t)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : List Bool)
    (store : SubexpRawTemplate.Store) (q : ℕ)
    (preparation : SubexpBlueprintFactor.Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (baseWidth p (D + 1)))
    (hc : SubexpTemplateData.ContextGood preparation source target minusOne)
    (bs : List (SubexpTemplateData.Block p D))
    (hq : SubexpTemplateCostBounds.TaylorBound q bs)
    (hraw : SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock) =
      SubexpRawTemplate.outputBytes packing t items (outerBanks e) (innerBanks e))
    (ctx : SubexpMomentSourceProgram.Context) (d : SubexpNodeWorkerBound.Data)
    (hprepared : ctx.template = SubexpTemplateExecution.output preparation source target minusOne bs) :
    inputBound ctx ≤ 10^67 * (scale (p := p) packing items suffix store q ctx d)^34 *
      (e.iterationCount + 1)^8 := by
  let B := preparedSize (p := p) packing items suffix store q
  let S := scale (p := p) packing items suffix store q ctx d
  have hB : 1 ≤ B := by
    have h := boundarySize_pos (p := p) packing items suffix store
    dsimp [B, preparedSize]
    omega
  have hAS : sizeParameter ctx ≤ S := by dsimp [S, scale, suffixSize]; omega
  have hBS : B ≤ S := by dsimp [B, S, scale]; omega
  have hN := (template_bounds e packing items suffix store q preparation source target minusOne hc bs hq hraw).2
  rw [← hprepared] at hN
  exact source_arithmetic (sizeParameter ctx) B S (e.iterationCount+1) ctx.template.length
    hB (by omega) hAS hBS hN

private theorem suffix_arithmetic (A S X J N C : ℕ)
    (hAS : A ≤ S) (hN : N ≤ 10^67 * S^34 * J^8)
    (hC : C ≤ 20000000000 * A^14 * X^5 * N) :
    C ≤ 10^78 * S^48 * X^5 * J^8 := by
  apply hC.trans
  calc
    _ ≤ 20000000000 * S^14 * X^5 * (10^67 * S^34 * J^8) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hAS 14))) hN
    _ = (2 * 10^77) * (S^48 * X^5 * J^8) := by ring
    _ ≤ (10^78) * (S^48 * X^5 * J^8) := by
      have h : 2 * 10^77 ≤ (10^78 : ℕ) := by norm_num
      exact Nat.mul_le_mul_right (S^48 * X^5 * J^8) h
    _ = 10^78 * S^48 * X^5 * J^8 := by ring

/-- Substitute both actual template transformations into the entire
measured source/job/moment suffix. The expression-byte equality is retained
by the actual source execution theorem. -/
theorem jobsPhaseCost_le_iterations (e : SubexpLayoutSpec.EnumerationData L t)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : List Bool)
    (store : SubexpRawTemplate.Store) (q : ℕ)
    (preparation : SubexpBlueprintFactor.Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (baseWidth p (D + 1)))
    (hc : SubexpTemplateData.ContextGood preparation source target minusOne)
    (bs : List (SubexpTemplateData.Block p D))
    (hq : SubexpTemplateCostBounds.TaylorBound q bs)
    (hraw : SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock) =
      SubexpRawTemplate.outputBytes packing t items (outerBanks e) (innerBanks e))
    (ctx : SubexpMomentSourceProgram.Context) (d : SubexpNodeWorkerBound.Data)
    (hprepared : ctx.template = SubexpTemplateExecution.output preparation source target minusOne bs)
    (M : SubexpPreparedQuartic.Modulus p (ctx.dimension + 1))
    (reduction zero one : QuarticCode p ctx.dimension) (slots : List (RawIndex ctx.dimension))
    (inputs : List (SubexpMomentSourceProgram.BlockData ctx)) (bytes : List Bool → List Bool)
    (expr : (Fin ctx.dimension → ℕ) → Algorithm.Expr (CoeffList ctx.dimension (QuarticCode p ctx.dimension)))
    (htemplate : ctx.template = SubexpMomentSourceProgram.encodeTemplate
      (inputs.map SubexpMomentSourceProgram.BlockData.template))
    (hmaster : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords ctx.dimension))
    (hs : ∀ a ∈ slots, Retained ctx.dimension a) (hN : slots.length ≤ slotCount ctx.dimension)
    (hbytes : ∀ a : Fin ctx.dimension → ℕ, bytes (SubexpExponentController.momentWord a) =
      SubexpPostfixControl.serializeCode
        (SubexpDenseSerialization.encodeFixedQuarticCoefficients p ctx.dimension) (expr a).compile)
    (hsize : ∀ a : Fin ctx.dimension → ℕ, (bytes (SubexpExponentController.momentWord a)).length ≤
      SubexpMomentSourceProgram.uniformSourceBytes ctx inputs) :
    jobsPhaseCost p ctx M reduction zero one slots inputs bytes expr d ≤
      10^78 * (scale (p := p) packing items suffix store q ctx d)^48 *
        (monomialCount ctx.dimension)^5 * (e.iterationCount + 1)^8 := by
  have hinput := inputBound_le_iterations e packing items suffix store q preparation source target
    minusOne hc bs hq hraw ctx d hprepared
  have hcost := jobsPhaseCost_le_input p ctx M reduction zero one slots inputs bytes expr d
    htemplate hmaster hs hN hbytes hsize
  exact suffix_arithmetic (suffixSize p ctx d) (scale (p := p) packing items suffix store q ctx d)
    (monomialCount ctx.dimension) (e.iterationCount+1) (inputBound ctx) _
    (by unfold scale; omega) hinput hcost

theorem monomial_fifth_le (D : ℕ) : (monomialCount D)^5 ≤ 2^(128*D) := by
  by_cases hD : D = 0
  · subst D
    norm_num [monomialCount]
  · simpa only [MonomialCount.card_retainedX, monomialCount] using
      MonomialCount.card_retainedX_pow_five_le_budget D (by omega)

end SubexponentialSAT.SubexpNodeWorkerIterationBound

end OAI.Algorithms
