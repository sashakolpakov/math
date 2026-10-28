import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateBounds
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateContext
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingBounds

namespace OAI.Algorithms

/-! Polynomial bounds for the full measured color iteration.  Assignment,
packet, metadata and bank sizes are actual encoded input lengths. -/

namespace SubexponentialSAT.SubexpRawTemplateCostBounds

open scoped BigOperators

open SubexpRawTemplate
open Subexp.ConstructivePacking

variable {D r Q Δ : ℕ}

def inputSize
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) : ℕ :=
  (SubexpRawTemplateBounds.bankMaster bases inners).length +
  (SubexpFactorRoutingTraversal.words items ++ suffix).length +
  (Encoding.encodeList id (items.map Prod.snd)).length +
  (Subexp.SupportSelectionProgram.metadataTable P).length + D + Q + r + 1

theorem factorCost_le_runtimeBound (t : Fin Q) (g : Fin r)
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word) :
    factorCost t g items suffix (colorWord g.val) ≤
      SubexpFactorRoutingBounds.runtimeBound
        (SubexpFactorRoutingTraversal.words items ++ suffix).length
        (Encoding.encodeList id (items.map Prod.snd)).length
        (colorWord g.val).length t.val Q r := by
  have hl := SubexpFactorRoutingBounds.budget_le t g items
  have ho := SubexpFactorRoutingBounds.retained_length_le t g items
  have hs : suffix.length ≤ (SubexpFactorRoutingTraversal.words items ++ suffix).length := by
    simp only [List.length_append]
    omega
  have hc : CounterConversions.runtimeBound (colorWord g.val) ≤
      32 * (r+1) * ((colorWord g.val).length+1) := by
    unfold CounterConversions.runtimeBound
    rw [colorWord_value]
    gcongr
    exact g.isLt.le
  have ht := t.isLt
  have hg := g.isLt
  unfold factorCost SubexpFactorRoutingBounds.runtimeBound
  rw [SubexpFactorRoutingBounds.encoded_reverse_length]
  omega

private theorem runtimeBound_le_cube (A F b t Q r N : ℕ)
    (hN : 1 ≤ N) (hA : A ≤ N) (hF : F ≤ N) (hb : b+1 ≤ N)
    (ht : t ≤ N) (hQ : Q+1 ≤ N) (hr : r+1 ≤ N) :
    SubexpFactorRoutingBounds.runtimeBound A F b t Q r ≤ 400*N^3 := by
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith
  have h1 : 7*(A+F+b+t) ≤ 28*N := by omega
  have h2 : 32*(r+1)*(b+1) ≤ 32*N^2 := by
    calc
      _ ≤ 32*N*N := by gcongr
      _ = _ := by ring
  have h3 : F*(200*(Q+1)*(r+1)+11) ≤ 211*N^3 := by
    calc
      _ ≤ N*(200*N*N+11) := by gcongr
      _ ≤ 211*N^3 := by nlinarith
  have h4 : 10*F+2*A+2*r+2*Q+60 ≤ 76*N := by omega
  unfold SubexpFactorRoutingBounds.runtimeBound
  nlinarith

/-- Bound the actual per-color parser, both selectors, term construction,
group framing and clearing, and the physical binary-counter increment. -/
theorem groupStepCost_le (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (g : Fin r) (increments : List Word)
    (hi : (Encoding.encodeList id increments).length ≤
      (SubexpRawTemplateBounds.bankMaster bases inners).length) :
    groupStepCost P t items suffix g increments ≤
      1000000*(inputSize P items suffix bases inners)^3 := by
  let N := inputSize P items suffix bases inners
  have hN : 1 ≤ N := by dsimp [N, inputSize]; omega
  have hA : (SubexpFactorRoutingTraversal.words items ++ suffix).length ≤ N := by
    dsimp [N, inputSize]; omega
  have hF : (Encoding.encodeList id (items.map Prod.snd)).length+1 ≤ N := by
    dsimp [N, inputSize]; omega
  have hD : D+1 ≤ N := by dsimp [N, inputSize]; omega
  have hQ : Q+1 ≤ N := by dsimp [N, inputSize]; omega
  have hr : r+1 ≤ N := by dsimp [N, inputSize]; omega
  have hI : (Encoding.encodeList id increments).length ≤ N := by
    dsimp [N, inputSize]; omega
  have ht : t.val ≤ Q := t.isLt.le
  have hg : g.val ≤ r := g.isLt.le
  have hbits := colorWord_length g.val
  have hN2 : N ≤ N^2 := by nlinarith
  have hN3 : N^2 ≤ N^3 := by nlinarith
  have hfactor : factorCost t g items suffix (colorWord g.val) ≤ 400*N^3 := by
    apply (factorCost_le_runtimeBound t g items suffix).trans
    exact runtimeBound_le_cube _ _ _ _ _ _ N hN hA (by omega)
      (by omega) (by omega) hQ hr
  have hselector : Subexp.SupportSelectionProgram.budget
      (Subexp.SupportSelectionProgram.metadataTable P).length D t.val r (colorWord g.val) ≤
      216000*N^3 := by
    apply (Subexp.SupportSelectionProgram.budget_le_polynomial _ _ _ _ _).trans
    have hs : (Subexp.SupportSelectionProgram.metadataTable P).length+D+t.val+r+
        CounterPrograms.value (colorWord g.val)+(colorWord g.val).length+1 ≤ 3*N := by
      rw [colorWord_value]
      dsimp [N, inputSize]
      omega
    calc
      _ ≤ 8000*(3*N)^3 := by gcongr
      _ = _ := by ring
  have hs : (selectedSupport P t g.val).length ≤ 2*N^2 := by
    apply (SubexpRawTemplateBounds.selectedIndexBytes_le
      (Subexp.SupportSelectionProgram.colorTest P t g.val) D).trans
    gcongr
  have ho : (selectedOutside P).length ≤ 2*N^2 := by
    apply (SubexpRawTemplateBounds.selectedIndexBytes_le
      (Subexp.SupportSelectionProgram.outsideTest P) D).trans
    gcongr
  have hf : (routedBytes t g items).length+1 ≤ N := by
    have hp := SubexpFactorRoutingBounds.retained_length_le t g items
    change (routedBytes t g items).length ≤ _ at hp
    omega
  have hw : (selectedSupport P t g.val).length+(routedBytes t g items).length+1 ≤ 3*N^2 := by
    omega
  have hgroup : groupCost (selectedSupport P t g.val) (routedBytes t g items) increments ≤
      300*N^3 := by
    apply (SubexpRawTemplateBounds.groupCost_le _ _ _).trans
    calc
      _ ≤ 100*(3*N^2)*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hw) hI
      _ = _ := by ring
  have hbytes : (colorGroupBytes P t items g increments).length ≤ 12*N^3 := by
    apply (SubexpRawTemplateBounds.groupBytes_le _ _ _).trans
    calc
      _ ≤ 4*(3*N^2)*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hw) hI
      _ = _ := by ring
  have hcounter : CounterPrograms.rippleCost true (colorWord g.val)+1 ≤ 8*N := by
    have hc := CounterPrograms.rippleCost_le true (colorWord g.val)
    omega
  unfold groupStepCost
  change _ ≤ 1000000*N^3
  nlinarith

theorem innerBank_le_master (bases : List Word) (inners : List (List Word))
    (increments : List Word) (hi : increments ∈ inners) :
    (Encoding.encodeList id increments).length ≤
      (SubexpRawTemplateBounds.bankMaster bases inners).length := by
  have hm : (Encoding.encodeList id increments).length ∈
      inners.map (fun xs => (SubexpRawTemplateBounds.encode xs).length) :=
    List.mem_map.mpr ⟨increments, hi, rfl⟩
  have hs := List.le_sum_of_mem hm
  rw [SubexpRawTemplateBounds.bankMaster_length]
  omega

/-- The ordered list of all color iterations includes both scan tests for
each record and the final test; it has degree four in actual input size. -/
theorem colorLoopSum_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : Fin r → List Word) :
    (List.ofFn (fun g => groupStepCost P t items suffix g (inners g)+2)).sum+1 ≤
      1000003*(inputSize P items suffix bases (List.ofFn inners))^4 := by
  let N := inputSize P items suffix bases (List.ofFn inners)
  have hN : 1 ≤ N := by dsimp [N, inputSize]; omega
  have hr : r ≤ N := by dsimp [N, inputSize]; omega
  have hp : ∀ g : Fin r, groupStepCost P t items suffix g (inners g)+2 ≤ 1000000*N^3+2 := by
    intro g
    have hm : inners g ∈ List.ofFn inners := List.mem_ofFn.mpr ⟨g, rfl⟩
    exact Nat.add_le_add_right (groupStepCost_le P t items suffix bases (List.ofFn inners)
      g (inners g) (innerBank_le_master bases (List.ofFn inners) (inners g) hm)) 2
  have hsum : (List.ofFn (fun g => groupStepCost P t items suffix g (inners g)+2)).sum ≤
      r*(1000000*N^3+2) := by
    rw [List.sum_ofFn]
    calc
      _ ≤ ∑ _g : Fin r, (1000000*N^3+2) := Finset.sum_le_sum (fun g _ => hp g)
      _ = _ := by simp
  have hN4 : N ≤ N^4 := by
    exact Nat.le_self_pow (by decide) N
  have hx : r*(1000000*N^3+2) ≤ 1000000*N^4+2*N := by
    calc
      _ ≤ N*(1000000*N^3+2) := Nat.mul_le_mul_right _ hr
      _ = _ := by ring
  change _ ≤ 1000003*N^4
  omega

end SubexponentialSAT.SubexpRawTemplateCostBounds

end OAI.Algorithms
