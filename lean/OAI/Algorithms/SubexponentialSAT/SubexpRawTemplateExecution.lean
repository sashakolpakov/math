import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateColors
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateBoundary

namespace OAI.Algorithms

/-!
# Complete execution of the raw template producer

The only list inputs are the actual bank bundle, the full original factor
packet stream, and immutable assignment/packing masters. Supports and color
factor lists are computed by the concrete selectors inside the program.
-/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.ConstructivePacking

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {D r Q Δ : ℕ}

structure Ready (store : Store) : Prop extends ColorWork store where
  bases : store 205 = []
  outsideMaster : store 208 = []
  groupRecords : store 211 = []
  groups : store 212 = []
  block : store 217 = []
  color : store 219 = []
  blocks : store 221 = []
  output : store 15 = []

def bankBundle (bases : List Word) (inners : List (List Word)) : Word :=
  Encoding.encodeList id (Encoding.encodeList id bases :: inners.map (Encoding.encodeList id))

def outputBytes
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (bases : List Word) (inners : List (List Word)) : Word :=
  blocksBytes (selectedOutside P) (Encoding.encodeList id (groupsFrom P t items 0 inners)) bases

def commandCost
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (store : Store) : ℕ :=
  outsideCost P t + (9 * (Encoding.encodeList id bases).length + 8) +
  (2 + groupScanCost P t items suffix 0 inners) +
  closeCost (groupsFrom P t items 0 inners) inners.length +
  outerCost (selectedOutside P) (Encoding.encodeList id (groupsFrom P t items 0 inners)) bases +
  (2 * (selectedOutside P).length +
    2 * (Encoding.encodeList id (groupsFrom P t items 0 inners)).length +
    2 * (Encoding.encodeList id (items.map Prod.snd)).length +
    2 * (store 226).length + 2 * (store 227).length + 15)

def resultStore (store : Store) (bits : Word) : Store :=
  Function.update (Function.update (Function.update
    (Function.update (Function.update store 15 bits) 204 []) 225 []) 226 []) 227 []

private def groupsReadyStore (store : Store) (bases outside groups : Word) : Store :=
  Function.update (Function.update (Function.update
    (Function.update store 204 []) 205 bases) 208 outside) 212 groups

private theorem encodeBankTail (inners : List (List Word)) :
    Encoding.encodeList id (inners.map (Encoding.encodeList id)) =
      Encoding.encodeList (Encoding.encodeList id) inners := by
  induction inners with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

/-- All generated temporary masters are physically consumed or cleared.
The exact final map also frames every immutable and unrelated worker port. -/
theorem command_eval
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (hlen : inners.length ≤ r)
    (d : Data) (hm : Masters P t items suffix d.stacks) (hw : Ready d.stacks)
    (h204 : d.stacks 204 = bankBundle bases inners) :
    ∃ n e, n ≤ commandCost P t items suffix bases inners d.stacks ∧
      Eval command n d e ∧ e.stacks = resultStore d.stacks (outputBytes P t items bases inners) := by
  let outside := selectedOutside P
  let groups := groupsFrom P t items 0 inners
  let groupCode := Encoding.encodeList id groups
  let baseCode := Encoding.encodeList id bases
  obtain ⟨na, a, hna, ha, has⟩ := initializeOutside_eval P t items suffix d hm
    hw.toColorWork hw.outsideMaster hw.color
  let b := splitResult baseCode
    (Encoding.encodeList id (inners.map (Encoding.encodeList id))) a
  have hb : Eval splitBanks (9 * baseCode.length + 8) a b :=
    splitBanks_eval baseCode (inners.map (Encoding.encodeList id)) a
      (by simpa [has, bankBundle, baseCode] using h204)
      (by simpa [has] using hw.bases) (by simpa [has] using hw.scratch)
  have hmb : Masters P t items suffix b.stacks := by
    apply hm.of_frame
    intro i hi
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [b, splitResult, has]
  have hwb : ColorWork b.stacks := by
    constructor
    · intro i hlo hhi
      have h204 : i ≠ 204 := by intro h; subst i; norm_num at hhi
      have h205 : i ≠ 205 := by intro h; subst i; norm_num at hhi
      have h208 : i ≠ 208 := by intro h; subst i; norm_num at hhi
      simpa [b, splitResult, has, h204, h205, h208] using hw.workspace i hlo hhi
    · simpa [b, splitResult, has] using hw.bank
    · simpa [b, splitResult, has] using hw.payload
    · simpa [b, splitResult, has] using hw.support
    · simpa [b, splitResult, has] using hw.factors
    · simpa [b, splitResult, has] using hw.term
    · simpa [b, splitResult, has] using hw.terms
    · simpa [b, splitResult, has] using hw.group
    · simpa [b, splitResult, has] using hw.scratch
    · simpa [b, splitResult, has] using hw.outside
    · simpa [b, splitResult, has] using hw.forward
  have hbcolor : b.stacks 219 = colorWord 0 := by
    simpa [b, splitResult, has, colorWord] using hw.color
  obtain ⟨nc, rc, hnc, hc⟩ := colors_eval P t items suffix inners 0 (by simpa using hlen)
    b.regs b.stacks [] hmb hwb hbcolor
  have hstart : inputState 204 b.regs b.stacks
      (Encoding.encodeList (Encoding.encodeList id) inners ++ []) = b := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 204
      · subst i; simp [inputState, b, splitResult, encodeBankTail]
      · simp [inputState, hi]
  rw [hstart] at hc
  let c := inputState 204 rc (groupsStore P t items 0 inners b.stacks) []
  have hc211 : c.stacks 211 = (recordBytes id groups).reverse := by
    simp [c, inputState, groupsStore, groups, b, splitResult, has, hw.groupRecords]
  have hc212 : c.stacks 212 = [] := by
    simpa [c, inputState, groupsStore, b, splitResult, has] using hw.groups
  have hc219 : c.stacks 219 = colorWord inners.length := by
    simp [c, inputState, groupsStore]
  obtain ⟨e, he, hes⟩ := closeGroups_eval groups inners.length c hc211 hc212 hc219
  have heReady : e.stacks = groupsReadyStore d.stacks baseCode outside groupCode := by
    rw [hes]
    funext i
    by_cases hi204 : i = 204
    · subst i; simp [c, inputState, groupsReadyStore]
    by_cases hi205 : i = 205
    · subst i; simp [c, inputState, groupsStore, b, splitResult, groupsReadyStore]
    by_cases hi208 : i = 208
    · subst i; simp [c, inputState, groupsStore, b, splitResult, has, groupsReadyStore, outside]
    by_cases hi211 : i = 211
    · subst i; simp [groupsReadyStore, hw.groupRecords]
    by_cases hi212 : i = 212
    · subst i; simp [groupsReadyStore, groupCode]
    by_cases hi219 : i = 219
    · subst i; simp [groupsReadyStore, hw.color]
    · simp [c, inputState, groupsStore, b, splitResult, has, groupsReadyStore,
        hi204, hi205, hi208, hi211, hi212, hi219]
  have heOuter : OuterWork outside groupCode e.stacks := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [heReady, groupsReadyStore] using hw.payload
    · simpa [heReady, groupsReadyStore] using hw.block
    · simpa [heReady, groupsReadyStore] using hw.scratch
    · simpa [heReady, groupsReadyStore] using hw.forward
    · simp [heReady, groupsReadyStore]
    · simp [heReady, groupsReadyStore]
  obtain ⟨nf, f, hnf, hf, hfs⟩ := outer_eval outside groupCode bases e
    (by simp [heReady, groupsReadyStore, baseCode]) heOuter
    (by simpa [heReady, groupsReadyStore] using hw.blocks)
    (by simpa [heReady, groupsReadyStore] using hw.output)
  obtain ⟨v, hv, hvs⟩ := cleanup_eval f
  have hclean : cleanupCost f.stacks =
      2 * outside.length + 2 * groupCode.length +
      2 * (Encoding.encodeList id (items.map Prod.snd)).length +
      2 * (d.stacks 226).length + 2 * (d.stacks 227).length + 15 := by
    simp [cleanupCost, hfs, heReady, groupsReadyStore, hm.packets]
  rw [hclean] at hv
  have hall := ha.seq (hb.seq (hc.seq (he.seq (hf.seq hv))))
  refine ⟨_, v, ?_, hall, ?_⟩
  · dsimp [commandCost, baseCode, outside, groupCode, groups] at ⊢
    dsimp [outside, groupCode, groups] at hnf
    dsimp [groups] at he
    omega
  · rw [hvs, hfs, heReady]
    funext i
    by_cases hi15 : i = 15
    · subst i; simp [cleanedStore, groupsReadyStore, resultStore, outputBytes, outside, groupCode, groups]
    by_cases hi204 : i = 204
    · subst i; simp [cleanedStore, groupsReadyStore, resultStore]
    by_cases hi205 : i = 205
    · subst i; simp [cleanedStore, groupsReadyStore, resultStore, hw.bases]
    by_cases hi208 : i = 208
    · subst i; simp [cleanedStore, groupsReadyStore, resultStore, hw.outsideMaster]
    by_cases hi212 : i = 212
    · subst i; simp [cleanedStore, groupsReadyStore, resultStore, hw.groups]
    by_cases hi225 : i = 225
    · subst i; simp [cleanedStore, resultStore]
    by_cases hi226 : i = 226
    · subst i; simp [cleanedStore, resultStore]
    by_cases hi227 : i = 227
    · subst i; simp [cleanedStore, resultStore]
    · simp [cleanedStore, groupsReadyStore, resultStore,
        hi15, hi204, hi205, hi208, hi212, hi225, hi226, hi227]

/-- A single finite program executes the full expansion for every runtime
number of colors and every finite bank/factor input. -/
theorem program_runs
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (hlen : inners.length ≤ r)
    (d : Data) (hm : Masters P t items suffix d.stacks) (hw : Ready d.stacks)
    (h204 : d.stacks 204 = bankBundle bases inners) :
    ∃ e : Data, RunsIn program (commandCost P t items suffix bases inners d.stacks + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = resultStore d.stacks (outputBytes P t items bases inners) := by
  obtain ⟨n, e, hn, he, hs⟩ := command_eval P t items suffix bases inners hlen d hm hw h204
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 204 15⟩, hs⟩

/-- The same concrete execution transported to the fixed primitive machine. -/
theorem program_primitive
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word)
    (bases : List Word) (inners : List (List Word)) (hlen : inners.length ≤ r)
    (d : Data) (hm : Masters P t items suffix d.stacks) (hw : Ready d.stacks)
    (h204 : d.stacks 204 = bankBundle bases inners) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program *
        (commandCost P t items suffix bases inners d.stacks + 1))
      (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (e.withPC none)) ∧
      e.stacks = resultStore d.stacks (outputBytes P t items bases inners) := by
  obtain ⟨e, he, hs⟩ := program_runs P t items suffix bases inners hlen d hm hw h204
  exact ⟨e, BitProgram.primitive_execution program he, hs⟩

theorem result_frame (store : Store) (bits : Word) (i : Fin 288)
    (h15 : i ≠ 15) (h204 : i ≠ 204) (h225 : i ≠ 225) (h226 : i ≠ 226) (h227 : i ≠ 227) :
    resultStore store bits i = store i := by
  simp [resultStore, h15, h204, h225, h226, h227]

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
