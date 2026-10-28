import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateCostBounds
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateExecution

namespace OAI.Algorithms

/-! The complete raw-template program has a fixed-degree bound in its
physical input lengths, including the two temporary stacks it clears. -/

namespace SubexponentialSAT.SubexpRawTemplateProgramBounds

open BitProgram StructuredCalls SubexpRawTemplate SubexpRawTemplateCostBounds
open Subexp.ConstructivePacking

variable {D r Q Δ : ℕ}

def totalSize
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (store : Store) : ℕ :=
  inputSize P items suffix bases inners + (store 226).length + (store 227).length

private theorem scan_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (remaining : List (List Word)) (K : ℕ) :
    ∀ start, (∀ g : Fin r, ∀ xs ∈ remaining, groupStepCost P t items suffix g xs ≤ K) →
      groupScanCost P t items suffix start remaining ≤ (K+2)*remaining.length := by
  induction remaining with
  | nil => intro start h; simp [groupScanCost]
  | cons xs remaining ih =>
      intro start h
      by_cases hg : start < r
      · have hh := h ⟨start, hg⟩ xs (by simp)
        have ht := ih (start+1) (fun g ys hy => h g ys (by simp [hy]))
        simp only [groupScanCost, dite_eq_left hg, List.length_cons]
        nlinarith
      · simp [groupScanCost, hg]

theorem groupScanCost_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (start : ℕ) :
    groupScanCost P t items suffix start inners ≤
      (1000000*(inputSize P items suffix bases inners)^3+2)*inners.length := by
  apply scan_le
  intro g xs hx
  exact groupStepCost_le P t items suffix bases inners g xs
    (innerBank_le_master bases inners xs hx)

theorem groupsFrom_length_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (inners : List (List Word)) (start : ℕ) :
    (groupsFrom P t items start inners).length ≤ inners.length := by
  induction inners generalizing start with
  | nil => simp [groupsFrom]
  | cons xs inners ih =>
      by_cases hg : start < r
      · simpa only [groupsFrom, dite_eq_left hg, List.length_cons] using
          Nat.succ_le_succ (ih (start+1))
      · simp [groupsFrom, hg]

private theorem groupLengthSum_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (inners : List (List Word)) (start : ℕ) :
    ((groupsFrom P t items start inners).map List.length).sum ≤
      4*(2*(D+1)^2+(Encoding.encodeList id (items.map Prod.snd)).length+1)*
        (inners.map (fun xs => (Encoding.encodeList id xs).length)).sum := by
  induction inners generalizing start with
  | nil => simp [groupsFrom]
  | cons xs inners ih =>
      by_cases hg : start < r
      · have hs := SubexpRawTemplateBounds.selectedIndexBytes_le
          (Subexp.SupportSelectionProgram.colorTest P t start) D
        have hf := SubexpFactorRoutingBounds.retained_length_le t ⟨start, hg⟩ items
        have hh : (colorGroupBytes P t items ⟨start, hg⟩ xs).length ≤
            4*(2*(D+1)^2+(Encoding.encodeList id (items.map Prod.snd)).length+1)*
              (Encoding.encodeList id xs).length := by
          apply (SubexpRawTemplateBounds.groupBytes_le (selectedSupport P t start)
            (routedBytes t ⟨start, hg⟩ items) xs).trans
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          exact Nat.add_le_add_right (Nat.add_le_add hs hf) 1
        have ht := ih (start+1)
        simp only [groupsFrom, dite_eq_left hg, List.map_cons, List.sum_cons]
        nlinarith
      · simp [groupsFrom, hg]

theorem groupsFrom_encoded_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (bases : List Word) (inners : List (List Word)) (start : ℕ) :
    (Encoding.encodeList id (groupsFrom P t items start inners)).length ≤
      4*(2*(D+1)^2+(Encoding.encodeList id (items.map Prod.snd)).length+1)*
        (SubexpRawTemplateBounds.bankMaster bases inners).length := by
  have hs := groupLengthSum_le P t items inners start
  have hl := groupsFrom_length_le P t items inners start
  rw [SubexpRawTemplateBounds.encoded_length, SubexpRawTemplateBounds.bankMaster_length]
  ring_nf at hs ⊢
  omega

/-- The full controller, all scans and clear operations, and final halt
fit a degree-four envelope. No generated-size or execution-cost premise is
supplied by the caller. -/
theorem commandCost_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (hlen : inners.length ≤ r)
    (store : Store) :
    commandCost P t items suffix bases inners store+1 ≤
      2000000*(totalSize P items suffix bases inners store)^4 := by
  let N := totalSize P items suffix bases inners store
  have hN : 1 ≤ N := by dsimp [N, totalSize, inputSize]; omega
  have hN2 : N ≤ N^2 := Nat.le_self_pow (by decide) N
  have hN3 : N^2 ≤ N^3 := by nlinarith
  have hN4 : N^3 ≤ N^4 := by nlinarith
  have hD : D+1 ≤ N := by dsimp [N, totalSize, inputSize]; omega
  have hF : (Encoding.encodeList id (items.map Prod.snd)).length+1 ≤ N := by
    dsimp [N, totalSize, inputSize]; omega
  have hB : (SubexpRawTemplateBounds.bankMaster bases inners).length ≤ N := by
    dsimp [N, totalSize, inputSize]; omega
  have hC : inners.length ≤ N := by dsimp [N, totalSize, inputSize]; omega
  have hE : (Encoding.encodeList id bases).length ≤ N := by
    have hb := SubexpRawTemplateBounds.bankMaster_length bases inners
    simp only [SubexpRawTemplateBounds.encode] at hb
    omega
  have hT : (store 226).length+(store 227).length ≤ N := by
    dsimp [N, totalSize]; omega
  have hsmall : inputSize P items suffix bases inners ≤ N := by
    dsimp [N, totalSize]; omega
  have hs : (selectedSupport P t 0).length ≤ 2*N^2 := by
    apply (SubexpRawTemplateBounds.selectedIndexBytes_le
      (Subexp.SupportSelectionProgram.colorTest P t 0) D).trans
    gcongr
  have ho : (selectedOutside P).length ≤ 2*N^2 := by
    apply (SubexpRawTemplateBounds.selectedIndexBytes_le
      (Subexp.SupportSelectionProgram.outsideTest P) D).trans
    gcongr
  have hW : 2*(D+1)^2+(Encoding.encodeList id (items.map Prod.snd)).length+1 ≤ 3*N^2 := by
    have hD2 := Nat.pow_le_pow_left hD 2
    omega
  have hG : (Encoding.encodeList id (groupsFrom P t items 0 inners)).length ≤ 12*N^3 := by
    apply (groupsFrom_encoded_le P t items bases inners 0).trans
    calc
      _ ≤ 4*(3*N^2)*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hW) hB
      _ = _ := by ring
  have hselection : Subexp.SupportSelectionProgram.budget
      (Subexp.SupportSelectionProgram.metadataTable P).length D t.val r [] ≤ 8000*N^3 := by
    apply (Subexp.SupportSelectionProgram.budget_le_polynomial _ _ _ _ _).trans
    have ht := t.isLt
    have hm : (Subexp.SupportSelectionProgram.metadataTable P).length+D+t.val+r+
        CounterPrograms.value ([] : Word)+([] : Word).length+1 ≤ N := by
      simp only [CounterPrograms.value, List.length_nil]
      dsimp [N, totalSize, inputSize]
      omega
    gcongr
  have houtside : outsideCost P t ≤ 8025*N^3 := by
    unfold outsideCost
    omega
  have hscan : groupScanCost P t items suffix 0 inners ≤ 1000000*N^4+2*N := by
    apply (groupScanCost_le P t items suffix bases inners 0).trans
    calc
      _ ≤ (1000000*N^3+2)*N := by gcongr
      _ = _ := by ring
  have hclose : closeCost (groupsFrom P t items 0 inners) inners.length ≤ 50*N^3 := by
    have hc := colorWord_length inners.length
    unfold closeCost
    omega
  have hag : (selectedOutside P).length+
      (Encoding.encodeList id (groupsFrom P t items 0 inners)).length+1 ≤ 15*N^3 := by
    omega
  have houter : outerCost (selectedOutside P)
      (Encoding.encodeList id (groupsFrom P t items 0 inners)) bases ≤ 1500*N^4 := by
    apply (SubexpRawTemplateBounds.outerCost_le _ _ _).trans
    calc
      _ ≤ 100*(15*N^3)*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hag) hE
      _ = _ := by ring
  unfold commandCost
  change _ ≤ 2000000*N^4
  omega

theorem outputBytes_length_le
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (store : Store) :
    (outputBytes P t items bases inners).length ≤
      60*(totalSize P items suffix bases inners store)^4 := by
  let N := totalSize P items suffix bases inners store
  have hN : 1 ≤ N := by dsimp [N, totalSize, inputSize]; omega
  have hN2 : N ≤ N^2 := Nat.le_self_pow (by decide) N
  have hN3 : N^2 ≤ N^3 := by nlinarith
  have hD : D+1 ≤ N := by dsimp [N, totalSize, inputSize]; omega
  have hF : (Encoding.encodeList id (items.map Prod.snd)).length+1 ≤ N := by
    dsimp [N, totalSize, inputSize]; omega
  have hB : (SubexpRawTemplateBounds.bankMaster bases inners).length ≤ N := by
    dsimp [N, totalSize, inputSize]; omega
  have hE : (Encoding.encodeList id bases).length ≤ N := by
    have hb := SubexpRawTemplateBounds.bankMaster_length bases inners
    simp only [SubexpRawTemplateBounds.encode] at hb
    omega
  have ho : (selectedOutside P).length ≤ 2*N^2 := by
    apply (SubexpRawTemplateBounds.selectedIndexBytes_le
      (Subexp.SupportSelectionProgram.outsideTest P) D).trans
    gcongr
  have hW : 2*(D+1)^2+(Encoding.encodeList id (items.map Prod.snd)).length+1 ≤ 3*N^2 := by
    have hD2 := Nat.pow_le_pow_left hD 2
    omega
  have hG : (Encoding.encodeList id (groupsFrom P t items 0 inners)).length ≤ 12*N^3 := by
    apply (groupsFrom_encoded_le P t items bases inners 0).trans
    calc
      _ ≤ 4*(3*N^2)*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hW) hB
      _ = _ := by ring
  have hag : (selectedOutside P).length+
      (Encoding.encodeList id (groupsFrom P t items 0 inners)).length+1 ≤ 15*N^3 := by
    omega
  apply (SubexpRawTemplateBounds.blocksBytes_le _ _ _).trans
  calc
    _ ≤ 4*(15*N^3)*N := Nat.mul_le_mul (Nat.mul_le_mul_left _ hag) hE
    _ = _ := by dsimp [N]; ring

/-- This is the actual fixed-program execution theorem with the numeric
envelope substituted for its internally derived instruction count. -/
theorem program_runs_polynomial
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (hlen : inners.length ≤ r)
    (d : Data) (hm : Masters P t items suffix d.stacks) (hw : Ready d.stacks)
    (h204 : d.stacks 204 = bankBundle bases inners) :
    ∃ e : Data, RunsIn program (2000000*(totalSize P items suffix bases inners d.stacks)^4)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = resultStore d.stacks (outputBytes P t items bases inners) := by
  obtain ⟨e, ⟨n, hn, he⟩, hs⟩ := SubexpRawTemplate.program_runs
    P t items suffix bases inners hlen d hm hw h204
  exact ⟨e, ⟨n, hn.trans (commandCost_le P t items suffix bases inners hlen d.stacks), he⟩, hs⟩

/-- The primitive interpreter multiplier depends only on the one fixed
program. All growing input parameters remain inside the displayed degree. -/
theorem program_primitive_polynomial
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (hlen : inners.length ≤ r)
    (d : Data) (hm : Masters P t items suffix d.stacks) (hw : Ready d.stacks)
    (h204 : d.stacks 204 = bankBundle bases inners) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (2000000*(totalSize P items suffix bases inners d.stacks)^4))
      (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (e.withPC none)) ∧
      e.stacks = resultStore d.stacks (outputBytes P t items bases inners) := by
  obtain ⟨e, he, hs⟩ := program_runs_polynomial P t items suffix bases inners hlen d hm hw h204
  exact ⟨e, BitProgram.primitive_execution program he, hs⟩

end SubexponentialSAT.SubexpRawTemplateProgramBounds

end OAI.Algorithms
