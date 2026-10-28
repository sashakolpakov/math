import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankBounds
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateProgramBounds
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateCostBounds

namespace OAI.Algorithms

/-! Substituting actual enumeration banks in the raw and prepared template
programs.  The remaining boundary size lists only the non-bank inputs;
neither generated template bytes nor source code occur in that size. -/

namespace SubexponentialSAT.SubexpNodeTemplateIterationBound

open Subexp.ConstructivePacking SubexpNodeBankBounds
open SubexpRawTemplate SubexpRawTemplateProgramBounds
open Subexp.MatrixWordEncoding SubexpSelectedConversions SubexpLiftRing

abbrev Bits := List Bool

variable {p D k Δ r : ℕ} {τ : ℚ} [Fact p.Prime]
variable {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
variable {P : Factor.Pattern (Fin D) F} {c : SubexpLayoutSpec.Parameters p k Δ r τ}
variable {L : SubexpLayoutSpec.Layout (E := E) P c} {t : Fin c.Q}

/-- Actual non-bank inputs at the raw-template boundary.  The packet and
temporary bytes have their own preceding producer bounds. -/
def boundarySize {Q : ℕ}
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Bits)
    (store : Store) : ℕ :=
  (SubexpFactorRoutingTraversal.words items ++ suffix).length +
  (Encoding.encodeList id (items.map Prod.snd)).length +
  (Subexp.SupportSelectionProgram.metadataTable packing).length +
  (store 226).length + (store 227).length + D + Q + r + width p + 1

omit [Fact p.Prime] in
theorem boundarySize_pos
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : Bits)
    (store : Store) : 1 ≤ boundarySize (p := p) packing items suffix store := by
  unfold boundarySize
  omega

theorem totalSize_le (e : SubexpLayoutSpec.EnumerationData L t)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : Bits)
    (store : Store) :
    totalSize packing items suffix (outerBanks e) (innerBanks e) store ≤
      17 * (boundarySize (p := p) packing items suffix store)^2 * (e.iterationCount + 1) := by
  let B := boundarySize (p := p) packing items suffix store
  let J := e.iterationCount + 1
  have hB : 1 ≤ B := boundarySize_pos packing items suffix store
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hDw : D * width p + 1 ≤ B^2 := by
    have h : D + width p + 1 ≤ B := by dsimp [B, boundarySize]; omega
    have hp := Nat.pow_le_pow_left h 2
    nlinarith only [hp, Nat.zero_le (D^2), Nat.zero_le ((width p)^2),
      Nat.zero_le (D * width p)]
  have hbank := bankBundle_length_le e
  have hb : (bankBundle e).length ≤ 16 * B^2 * J := by
    apply hbank.trans
    change 16 * (D * width p + 1) * J ≤ 16 * B^2 * J
    gcongr
  have hrest : totalSize packing items suffix (outerBanks e) (innerBanks e) store ≤
      (bankBundle e).length + B := by
    unfold totalSize SubexpRawTemplateCostBounds.inputSize SubexpNodeBankBounds.bankBundle
    dsimp [B, boundarySize]
    omega
  have hBJ : B ≤ B^2 * J := by
    calc
      B = B * 1 := by omega
      _ ≤ B^2 * J := Nat.mul_le_mul (Nat.le_self_pow (by decide) B) hJ
  change _ ≤ 17 * B^2 * J
  nlinarith only [hrest, hb, hBJ]

theorem rawCommandCost_le (e : SubexpLayoutSpec.EnumerationData L t)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : Bits)
    (store : Store) :
    commandCost packing t items suffix (outerBanks e) (innerBanks e) store + 1 ≤
      167042000000 * (boundarySize (p := p) packing items suffix store)^8 *
        (e.iterationCount + 1)^4 := by
  apply (SubexpRawTemplateProgramBounds.commandCost_le packing t items suffix
    (outerBanks e) (innerBanks e) (by simp [innerBanks]) store).trans
  calc
    _ ≤ 2000000 * (17 * (boundarySize (p := p) packing items suffix store)^2 *
        (e.iterationCount + 1))^4 := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (totalSize_le e packing items suffix store) 4)
    _ = _ := by ring

theorem rawOutputLength_le (e : SubexpLayoutSpec.EnumerationData L t)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : Bits)
    (store : Store) :
    (outputBytes packing t items (outerBanks e) (innerBanks e)).length ≤
      5011260 * (boundarySize (p := p) packing items suffix store)^8 *
        (e.iterationCount + 1)^4 := by
  apply (SubexpRawTemplateProgramBounds.outputBytes_length_le packing t items suffix
    (outerBanks e) (innerBanks e) store).trans
  calc
    _ ≤ 60 * (17 * (boundarySize (p := p) packing items suffix store)^2 *
        (e.iterationCount + 1))^4 := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (totalSize_le e packing items suffix store) 4)
    _ = _ := by ring

def preparedSize {Q : ℕ}
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Bits)
    (store : Store) (q : ℕ) : ℕ :=
  boundarySize (p := p) packing items suffix store + SubexpTemplateCostBounds.scale p D q

private theorem preparation_arithmetic (B S T J N : ℕ)
    (hB : 1 ≤ B) (hJ : 1 ≤ J) (hBS : B ≤ S) (hTS : T ≤ S)
    (hN : N ≤ 5011260 * B^8 * J^4) :
    10^20 * T^5 * (N+1) ≤ 10^27 * S^13 * J^4 := by
  have hpos : 1 ≤ B^8 * J^4 :=
    Nat.mul_le_mul (Nat.one_le_pow 8 B hB) (Nat.one_le_pow 4 J hJ)
  have hN1 : N+1 ≤ 5011261 * B^8 * J^4 := by nlinarith only [hN, hpos]
  have hN2 : N+1 ≤ 5011261 * S^8 * J^4 := by
    apply hN1.trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBS 8))
  calc
    _ ≤ 10^20 * S^5 * (5011261 * S^8 * J^4) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hTS 5)) hN2
    _ = (5011261 * 10^20) * (S^13 * J^4) := by ring
    _ ≤ 10^27 * S^13 * J^4 := by
      have h : 5011261 * 10^20 ≤ (10^27 : ℕ) := by norm_num
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (S^13 * J^4) h

private theorem prepared_factor_le (e : SubexpLayoutSpec.EnumerationData L t)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : Bits)
    (store : Store) (q : ℕ) (bs : List (SubexpTemplateData.Block p D))
    (hraw : SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock) =
      outputBytes packing t items (outerBanks e) (innerBanks e)) :
    10^20 * (SubexpTemplateCostBounds.scale p D q)^5 *
        (SubexpTemplateCostBounds.rawBytes bs + 1) ≤
      10^27 * (preparedSize (p := p) packing items suffix store q)^13 *
        (e.iterationCount + 1)^4 := by
  let B := boundarySize (p := p) packing items suffix store
  let S := preparedSize (p := p) packing items suffix store q
  let J := e.iterationCount + 1
  have hB : 1 ≤ B := boundarySize_pos packing items suffix store
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hBS : B ≤ S := by dsimp [B, S, preparedSize]; omega
  have hTS : SubexpTemplateCostBounds.scale p D q ≤ S := by
    dsimp [S, preparedSize]
    omega
  have ho : SubexpTemplateCostBounds.rawBytes bs ≤ 5011260 * B^8 * J^4 := by
    unfold SubexpTemplateCostBounds.rawBytes
    rw [hraw]
    exact rawOutputLength_le e packing items suffix store
  exact preparation_arithmetic B S (SubexpTemplateCostBounds.scale p D q) J
    (SubexpTemplateCostBounds.rawBytes bs) hB hJ hBS hTS ho

/-- Actual raw bytes from the enumeration are substituted into the
measured preparation service; only its genuine Taylor-depth condition is
needed in addition to the exact typed byte identity. -/
theorem template_bounds (e : SubexpLayoutSpec.EnumerationData L t)
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r c.Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r c.Q)) (suffix : Bits)
    (store : Store) (q : ℕ)
    (ctx : SubexpBlueprintFactor.Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (baseWidth p (D + 1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (bs : List (SubexpTemplateData.Block p D))
    (hq : SubexpTemplateCostBounds.TaylorBound q bs)
    (hraw : SubexpTemplateProgram.encodeBlocks (bs.map SubexpTemplateData.rawBlock) =
      outputBytes packing t items (outerBanks e) (innerBanks e)) :
    SubexpTemplateExecution.runCost ctx source target minusOne bs ≤
        10^27 * (preparedSize (p := p) packing items suffix store q)^13 *
          (e.iterationCount + 1)^4 ∧
    (SubexpTemplateExecution.output ctx source target minusOne bs).length ≤
        10^27 * (preparedSize (p := p) packing items suffix store q)^13 *
          (e.iterationCount + 1)^4 := by
  have hf := prepared_factor_le e packing items suffix store q bs hraw
  exact ⟨(SubexpTemplateCostBounds.runCost_le ctx source target minusOne hc q bs hq).trans hf,
    (SubexpTemplateCostBounds.output_length_le ctx source target minusOne hc q bs hq).trans hf⟩

end SubexponentialSAT.SubexpNodeTemplateIterationBound

end OAI.Algorithms
