import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySourceBank
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

/-! Actual produced ring, parked layout and source bytes at the current-query
high-loop entry. Every field is derived from the same executed preparation
and initializer; no new evaluator or preparation service is supplied. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryPreparedSource

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HighMarkedFrontend HighQuerySetup

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : State 40 896} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding

/-- The initializer changes only two lower words; all actual arithmetic and
parked source words have literal equality with the produced output. -/
theorem lower_frame (i : Fin 768) (h323 : i ≠ 323) (h330 : i ≠ 330) :
    (seeded).stacks (i.castAdd 128) = run.output.stacks i := by
  have hi : i.castAdd 128 ∉ ([330,788,789,790,323,791,792] : List (Fin 896)) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff,
      Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at *
    have := i.isLt
    omega
  rw [HighCountSeed.initialized_frame _ _ _ hi]
  exact result_stack front run.output i

/-- Every original ring-producer word below320 survives with the same bytes.
The statement includes both the framed and flat node tables. -/
theorem ring_word (i : Fin 320) :
    (seeded).stacks (i.castAdd 576) = run.ringState.stacks (i.castAdd 320) := by
  have hlow := run.arithmetic_output.low (i.castAdd 320) (by change i.val < 340; have := i.isLt; omega)
  have hf := lower_frame run (i.castAdd 448)
    (by intro h; have he := congrArg Fin.val h; have := i.isLt; simp only [Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at he; omega)
    (by intro h; have he := congrArg Fin.val h; have := i.isLt; simp only [Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at he; omega)
  exact hf.trans hlow

/-- Node-entry arithmetic caches are preserved as complete words. -/
theorem arithmetic_words (i : Fin 768) (hi : i ∈ QueryReadyConstruction.arithmeticPorts) :
    (seeded).stacks (i.castAdd 128) = run.output.stacks i := by
  apply lower_frame run i
  all_goals
    simp only [QueryReadyConstruction.arithmeticPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The node stream and interpolation table are the two actual serializations
of the same generated nodes, in their original increasing order. -/
theorem nodes :
    (seeded).stacks 300 = Encoding.encodeList id
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)) ∧
    (seeded).stacks 256 =
      (RingNodeMetadata.nodeBits ((model).val 33) ((model).val 34) ((model).val 21)).flatten := by
  exact ⟨(ring_word run 300).trans run.arithmetic_output.produced.framedNodes,
    (ring_word run 256).trans run.arithmetic_output.produced.flatNodes⟩

/-- The unary extension degree is the one physically produced before the
loop and used by every node's actual arithmetic. -/
theorem degree : (seeded).stacks 204 = List.replicate ((model).val 34) true :=
  (lower_frame run 204 (by decide) (by decide)).trans run.degree

/-- Parking preserves the actual addressed layout, including offset743 and
all neutral-factor metadata. No supplied successful layout is used. -/
theorem parked (i : Fin 14) :
    (seeded).stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)) =
      (PackingCallerProgram.result (project front) (packingProblem q k hg)
        run.first run.rest).stacks (LeafProgram.LayoutMasters.high i) := by
  have hi0 : LeafProgram.LayoutMasters.high i ≠ 323 := by
    intro h
    have he := congrArg Fin.val h
    change 730+i.val=323 at he
    omega
  have hi1 : LeafProgram.LayoutMasters.high i ≠ 330 := by
    intro h
    have he := congrArg Fin.val h
    change 730+i.val=330 at he
    omega
  exact (lower_frame run _ hi0 hi1).trans
    (NativeQueryPreparation.parked_result (project front) run.packed run.output
      (packingProblem q k hg) run.first run.rest run.packed_words run.arithmetic_output i)

/-- Source row, count and marker words remain the actual frontend's words. -/
theorem source_frame (i : Fin 768)
    (hi : i ∈ ([700,701,704,705,706,707,708,709] : List (Fin 768))) :
    (seeded).stacks (i.castAdd 128) = front.stacks (i.castAdd 128) := by
  have hlo : 660 ≤ i.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hf : run.output.stacks i = run.packed.stacks i := by
    apply run.arithmetic_output.highFrame i hlo
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rw [lower_frame run i (by intro h; subst i; simp at hi)
    (by intro h; subst i; simp at hi),hf,run.packed_words]
  change (PackingCallerProgram.result (project front) (packingProblem q k hg)
    run.first run.rest).stacks i = (project front).stacks i
  apply PackingCallerProgram.result_frame
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The actual frontend's row-count output survives the subsequent executed
packing, arithmetic and high-counter initialization. -/
theorem hash_count (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w) :
    (seeded).stacks 704 = List.replicate q.rows.length true :=
  (source_frame run 704 (by decide)).trans hf.hashCount

private theorem frontend_source_frame (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w) (i : Fin 768)
    (hi : i ∈ ([700,701,705,706,707,708,709] : List (Fin 768))) :
    front.stacks (i.castAdd 128) = base.stacks i := by
  apply hf.frame
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide

/-- These are the literal source and mark words consumed by the authentic
factor constructor. FrontState supplies the generated row count; original
entry readiness supplies only the input bytes. -/
theorem sources (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w) (hr : q.Ready base) :
    (seeded).stacks 700 = Encoding.encodeList id q.clauses ∧
    (seeded).stacks 701 = HashScopeProgram.RawTable.inputBits q.width.length q.rows ∧
    (seeded).stacks 704 = List.replicate q.rows.length true ∧
    (seeded).stacks 705 = q.index ∧ (seeded).stacks 706 = [q.mark.isSome] ∧
    (seeded).stacks 707 = q.modulus ∧ (seeded).stacks 708 = q.width ∧
    (seeded).stacks 709 = q.ambient := by
  rcases hr with ⟨h0,h1,h5,h6,h7,h8,h9,_,_,_,_⟩
  have hs (i : Fin 768) (hi : i ∈ ([700,701,705,706,707,708,709] : List (Fin 768))) :
      (seeded).stacks (i.castAdd 128) = base.stacks i := by
    have hi' : i ∈ ([700,701,704,705,706,707,708,709] : List (Fin 768)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      tauto
    exact (source_frame run i hi').trans (frontend_source_frame base w hf i hi)
  exact ⟨(hs 700 (by decide)).trans h0,(hs 701 (by decide)).trans h1,
    hash_count run base w hf,(hs 705 (by decide)).trans h5,(hs 706 (by decide)).trans h6,
    (hs 707 (by decide)).trans h7,(hs 708 (by decide)).trans h8,(hs 709 (by decide)).trans h9⟩

/-- Source-visible words at the actual seed endpoint have a cap independent
of all five suspended collector/selector words. The same produced witnesses
are retained; no shadow producer is chosen. -/
theorem visible_bound
    (hfront : ∀ i, ¬(i ∈ HighQueryProgram.Carried.words) → (front.stacks i).length ≤ S) :
    ∀ i, ¬(i ∈ HighQueryProgram.Carried.words) → ((seeded).stacks i).length ≤
      max (4 * BinaryArithmetic.toNat q.ambient + 1) (localBound S cost) := by
  have hp : ∀ i, ¬(i ∈ HighQueryProgram.Carried.words) →
      ((result front run.output).stacks i).length ≤ localBound S cost := by
    intro i hi
    have hx := trace_selectedStackBits (compiled HighQueryProgram.prepare 778 777) {i}
      (compiled_trace run.preparation 778 777)
    have hx' : ((preparedOutput front run.data.output).stacks i).length ≤
        (front.stacks i).length +
          (run.data.packingSteps + run.data.arithmeticSteps + 1) := by
      simpa only [selectedStackBits,Finset.sum_singleton] using hx
    have ht : run.data.packingSteps + run.data.arithmeticSteps ≤ cost :=
      run.preparation_time
    have hf := hfront i hi
    change ((preparedOutput front run.data.output).stacks i).length ≤ localBound S cost
    unfold localBound
    omega
  have hc := initialized_current_counter_length q (result front run.output)
    run.seedRegs run.mask
  intro i hi
  by_cases hchange : i ∈ ([330,788,789,790,323,791,792] : List (Fin 896))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hchange
    rcases hchange with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [HighQueryStart.initialized_lower_counter]
      exact hc.trans (Nat.le_max_left _ _)
    · rw [HighCountSeed.initialized_blank _ _ 788 (by decide)]
      exact Nat.zero_le _
    · exact hc.trans (Nat.le_max_left _ _)
    · rw [HighCountSeed.initialized_blank _ _ 790 (by decide)]
      exact Nat.zero_le _
    · rw [HighCountSeed.initialized_blank _ _ 323 (by decide)]
      exact Nat.zero_le _
    · rw [HighCountSeed.initialized_blank _ _ 791 (by decide)]
      exact Nat.zero_le _
    · rw [HighCountSeed.initialized_blank _ _ 792 (by decide)]
      exact Nat.zero_le _
  · rw [HighCountSeed.initialized_frame _ _ i hchange]
    exact (hp i hi).trans (Nat.le_max_right _ _)

/-- The current physical mask, rather than a mask shared by other marks,
remains available to each actual high decoder. -/
theorem mask : (seeded).stacks 338 =
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask (highSet q) := by
  rw [HighCountSeed.initialized_frame _ _ 338 (by decide)]
  change (preparedOutput front run.data.output).stacks 338 = _
  exact run.mask.trans (physical_high_mask q)

/-- The lower counter starts from the same attained all-zero tuple as the
durable counter. Later callbacks refresh it by the paid physical copy. -/
theorem counter : (seeded).stacks 330 =
    Encoding.encodeList id (List.replicate (highSet q).card [false]) :=
  (HighQueryStart.initialized_lower_counter _ _).trans run.counter

/-- The actual parked unary radius is the radius of the addressed native
input used at every node. It is derived from the executed frontend export. -/
theorem packed_radius (base : LeafProgram.Query.Data) (w : Bank.Words)
    (hf : FrontState q k base (project front) padding w)
    (node : Fin (packingProblem q k hg).Q) :
    (run.packed.stacks 740).length =
      (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg run.first run.rest node).R := by
  have he := packing_empty (project front) hf.privateEmpty hf.spare
  have hp := PackingCallerProgram.result_parameter (project front) (packingProblem q k hg)
    he run.first run.rest 10 (by decide) (by decide) (by decide)
  have hR : (model).val 29 = (produce (q.input k)).R :=
    (Execute.guardedModel_public (q.input k) padding 6).trans
      (Layout.model_core_values (q.input k) padding).2.2.2.2.2.2.1
  have hu := hf.exported.1 5
  have hw : run.packed.stacks 740 = List.replicate (produce (q.input k)).R true := by
    rw [run.packed_words]
    change (PackingCallerProgram.result (project front) (packingProblem q k hg)
      run.first run.rest).stacks (LeafProgram.LayoutMasters.high 10) = _
    rw [hp]
    simpa [Exports.destination,Exports.unaryValues,hR,LeafProgram.LayoutMasters.low] using hu
  rw [hw,List.length_replicate]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryPreparedSource
