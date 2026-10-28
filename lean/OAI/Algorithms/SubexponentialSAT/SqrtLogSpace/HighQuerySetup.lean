import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

abbrev Data := State 40 896
abbrev Lower := State 40 768

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

def localBound (S cost : ℕ) : ℕ := S + cost + 1

def boundaryBound (q : LeafQueryFrontend.Query) (S cost B : ℕ) : ℕ :=
  max (4 * BinaryArithmetic.toNat q.ambient + 1) (max (localBound S cost) B)

def prefixBound (q : LeafQueryFrontend.Query) (S cost B : ℕ) : ℕ :=
  max (12 * localBound S cost + 5) (boundaryBound q S cost B)

def preparedModel (q : LeafQueryFrontend.Query) (k : ℕ) (padding : Fin 8 → ℕ) :=
  Execute.guardedModel (q.input k) padding

noncomputable def preparedProblem (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) :=
  packingProblem q k hg

noncomputable def preparedOutput (front : Data) (output : Lower) : Data :=
  result front output

noncomputable def seededOutput (front : Data) (output : Lower)
    (seedRegs : Fin 2 → Bool) : Data :=
  HighCountSeed.initialized (preparedOutput front output) seedRegs

def inverseLaw (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (padding : Fin 8 → ℕ) (packed : Lower)
    (modulus : SubexpPreparedQuartic.Modulus 3 ((preparedModel q k padding).val 33))
    (cache : RingProgram.ScalarCache 3 ((preparedModel q k padding).val 33))
    (half : RingProgram.ScalarCode 3 ((preparedModel q k padding).val 33)) : Prop :=
  (RingProgram.modelRing ((preparedModel q k padding).val 33)
      (ring_precision_pos (q.input k) padding hg) (ring_degree_pos (q.input k) padding hg)
      (IrreducibleSearch.data (ring_degree_pos (q.input k) padding hg)) modulus cache).decode
      (LayoutDenominatorProgramQuery.value ((preparedModel q k padding).val 33)
        (IrreducibleSearch.data (ring_degree_pos (q.input k) padding hg)) modulus cache half
        (packed.stacks 740).length) *
      (2 : (IrreducibleSearch.data (ring_degree_pos (q.input k) padding hg)).O
        ((preparedModel q k padding).val 33)) ^ ((packed.stacks 740).length - 1) = 1

structure PackingData (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) where
  first : MulticolorTypes.Word (preparedProblem q k hg).r (preparedProblem q k hg).Q
  rest : List (MulticolorTypes.Word (preparedProblem q k hg).r (preparedProblem q k hg).Q)
  packed : Lower
  packingSteps : ℕ

def ArithmeticData (q : LeafQueryFrontend.Query) (k : ℕ)
    (padding : Fin 8 → ℕ) : Type :=
  ℕ × LeafRingSetupProgram.Data ×
    SubexpPreparedQuartic.Modulus 3 ((preparedModel q k padding).val 33) ×
    RingProgram.ScalarCache 3 ((preparedModel q k padding).val 33) ×
    RingProgram.ScalarCode 3 ((preparedModel q k padding).val 33) × Lower

namespace ArithmeticData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {padding : Fin 8 → ℕ}

abbrev arithmeticSteps (data : ArithmeticData q k padding) := data.1
abbrev ringState (data : ArithmeticData q k padding) := data.2.1
abbrev modulus (data : ArithmeticData q k padding) := data.2.2.1
abbrev cache (data : ArithmeticData q k padding) := data.2.2.2.1
abbrev half (data : ArithmeticData q k padding) := data.2.2.2.2.1
abbrev output (data : ArithmeticData q k padding) := data.2.2.2.2.2

end ArithmeticData

structure SeedData where
  seedSteps : ℕ
  seedRegs : Fin 2 → Bool

def PreparedData (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (padding : Fin 8 → ℕ) : Type :=
  PackingData q k hg × ArithmeticData q k padding × SeedData

namespace PreparedData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {padding : Fin 8 → ℕ}

abbrev packingData (data : PreparedData q k hg padding) := data.1
abbrev arithmeticData (data : PreparedData q k hg padding) := data.2.1
abbrev seedData (data : PreparedData q k hg padding) := data.2.2

abbrev first (data : PreparedData q k hg padding) := data.packingData.first
abbrev rest (data : PreparedData q k hg padding) := data.packingData.rest
abbrev packed (data : PreparedData q k hg padding) := data.packingData.packed
abbrev packingSteps (data : PreparedData q k hg padding) := data.packingData.packingSteps
abbrev arithmeticSteps (data : PreparedData q k hg padding) :=
  data.arithmeticData.arithmeticSteps
abbrev ringState (data : PreparedData q k hg padding) := data.arithmeticData.ringState
abbrev modulus (data : PreparedData q k hg padding) := data.arithmeticData.modulus
abbrev cache (data : PreparedData q k hg padding) := data.arithmeticData.cache
abbrev half (data : PreparedData q k hg padding) := data.arithmeticData.half
abbrev output (data : PreparedData q k hg padding) := data.arithmeticData.output
abbrev seedSteps (data : PreparedData q k hg padding) := data.seedData.seedSteps
abbrev seedRegs (data : PreparedData q k hg padding) := data.seedData.seedRegs

end PreparedData

structure PreparedExecution (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (front : Data) (padding : Fin 8 → ℕ)
    (data : PreparedData q k hg padding) : Prop where
  rows : (data.first :: data.rest).map Subexp.ReadPlan.encodeWord =
    Subexp.AssignmentAlphabetSemantics.wordBytes (preparedProblem q k hg).r
      (preparedProblem q k hg).Q
  nodup : (data.first :: data.rest).Nodup
  complete : ∀ z, z ∈ data.first :: data.rest
  packing : Eval PackingCallerProgram.command data.packingSteps (project front) data.packed
  packed_words : data.packed.stacks =
    (PackingCallerProgram.result (project front) (preparedProblem q k hg)
      data.first data.rest).stacks
  arithmetic : Eval NativeQueryPreparation.arithmeticCommand data.arithmeticSteps
    data.packed data.output
  arithmetic_output : ArithmeticOutput data.packed data.output (preparedModel q k padding)
    (ring_degree_pos (q.input k) padding hg) data.modulus data.cache data.half data.ringState
  degree : data.output.stacks 204 =
    List.replicate ((preparedModel q k padding).val 34) true
  inverse : inverseLaw q k hg padding data.packed data.modulus data.cache data.half
  preparation : Eval HighQueryProgram.prepare
    (data.packingSteps + data.arithmeticSteps + 1) front (preparedOutput front data.output)
  seed : Eval HighQueryProgram.seed data.seedSteps (preparedOutput front data.output)
    (seededOutput front data.output data.seedRegs)

structure PreparedResources (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (front : Data) (padding : Fin 8 → ℕ)
    (S B cost : ℕ) (data : PreparedData q k hg padding) : Prop where
  preparation_time : data.packingSteps + data.arithmeticSteps ≤ cost
  seed_time : data.seedSteps ≤ 110 * localBound S cost + 80
  guard : front.regs 8 = true
  mask : (preparedOutput front data.output).stacks 338 =
    LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)
  counter : (seededOutput front data.output data.seedRegs).stacks 789 =
    Encoding.encodeList id (List.replicate (highSet q).card [false])
  cleared : ∀ i ∈ ([788,790,323,791,792] : List (Fin 896)),
    (seededOutput front data.output data.seedRegs).stacks i = []
  high_guard : (seededOutput front data.output data.seedRegs).regs 21 = true
  kept : ∀ i, HashMarkedReturn.kept i = true →
    (seededOutput front data.output data.seedRegs).stacks i = front.stacks i
  boundary : ∀ i, ((seededOutput front data.output data.seedRegs).stacks i).length ≤
    boundaryBound q S cost B
  preparation_space : StageSpace HighQueryProgram.prepare
    (data.packingSteps + data.arithmeticSteps + 1) front (prefixBound q S cost B)
  seed_space : StageSpace HighQueryProgram.seed data.seedSteps (preparedOutput front data.output)
    (prefixBound q S cost B)
  prefix_space : StageSpace (.seq HighQueryProgram.prepare HighQueryProgram.seed)
    (data.packingSteps + data.arithmeticSteps + 1 + data.seedSteps + 1) front
    (prefixBound q S cost B)

/-- A factual output bundle for the fixed preparation and seed instructions.
All semantic objects and resource assertions refer to these same evaluations. -/
def PreparedRun (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (front : Data) (padding : Fin 8 → ℕ) (S B cost : ℕ) : Type :=
  { data : PreparedData q k hg padding //
    PreparedExecution q k hg front padding data ∧
      PreparedResources q k hg front padding S B cost data }

namespace PreparedRun

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}

abbrev data (run : PreparedRun q k hg front padding S B cost) := run.1
abbrev execution (run : PreparedRun q k hg front padding S B cost) := run.2.1
abbrev resources (run : PreparedRun q k hg front padding S B cost) := run.2.2

abbrev first (run : PreparedRun q k hg front padding S B cost) := run.data.first
abbrev rest (run : PreparedRun q k hg front padding S B cost) := run.data.rest
abbrev packed (run : PreparedRun q k hg front padding S B cost) := run.data.packed
abbrev packingSteps (run : PreparedRun q k hg front padding S B cost) := run.data.packingSteps
abbrev arithmeticSteps (run : PreparedRun q k hg front padding S B cost) :=
  run.data.arithmeticSteps
abbrev ringState (run : PreparedRun q k hg front padding S B cost) := run.data.ringState
abbrev modulus (run : PreparedRun q k hg front padding S B cost) := run.data.modulus
abbrev cache (run : PreparedRun q k hg front padding S B cost) := run.data.cache
abbrev half (run : PreparedRun q k hg front padding S B cost) := run.data.half
abbrev output (run : PreparedRun q k hg front padding S B cost) := run.data.output
abbrev seedSteps (run : PreparedRun q k hg front padding S B cost) := run.data.seedSteps
abbrev seedRegs (run : PreparedRun q k hg front padding S B cost) := run.data.seedRegs

abbrev rows (run : PreparedRun q k hg front padding S B cost) := run.execution.rows
abbrev nodup (run : PreparedRun q k hg front padding S B cost) := run.execution.nodup
abbrev complete (run : PreparedRun q k hg front padding S B cost) := run.execution.complete
abbrev packing (run : PreparedRun q k hg front padding S B cost) := run.execution.packing
abbrev packed_words (run : PreparedRun q k hg front padding S B cost) :=
  run.execution.packed_words
abbrev arithmetic (run : PreparedRun q k hg front padding S B cost) := run.execution.arithmetic
abbrev arithmetic_output (run : PreparedRun q k hg front padding S B cost) :=
  run.execution.arithmetic_output
abbrev degree (run : PreparedRun q k hg front padding S B cost) := run.execution.degree
abbrev inverse (run : PreparedRun q k hg front padding S B cost) := run.execution.inverse
abbrev preparation (run : PreparedRun q k hg front padding S B cost) :=
  run.execution.preparation
abbrev seed (run : PreparedRun q k hg front padding S B cost) := run.execution.seed

abbrev preparation_time (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.preparation_time
abbrev seed_time (run : PreparedRun q k hg front padding S B cost) := run.resources.seed_time
abbrev guard (run : PreparedRun q k hg front padding S B cost) := run.resources.guard
abbrev mask (run : PreparedRun q k hg front padding S B cost) := run.resources.mask
abbrev counter (run : PreparedRun q k hg front padding S B cost) := run.resources.counter
abbrev cleared (run : PreparedRun q k hg front padding S B cost) := run.resources.cleared
abbrev high_guard (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.high_guard
abbrev kept (run : PreparedRun q k hg front padding S B cost) := run.resources.kept
abbrev boundary (run : PreparedRun q k hg front padding S B cost) := run.resources.boundary
abbrev preparation_space (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.preparation_space
abbrev seed_space (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.seed_space
abbrev prefix_space (run : PreparedRun q k hg front padding S B cost) :=
  run.resources.prefix_space

end PreparedRun

/-- The measured prefix of the actual fixed successful branch. -/
theorem PreparedRun.eval {q k hg front padding S B cost}
    (run : PreparedRun q k hg front padding S B cost) :
    Eval (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) front
      (HighCountSeed.initialized (result front run.output) run.seedRegs) :=
  run.preparation.seq run.seed

theorem PreparedRun.time {q k hg front padding S B cost}
    (run : PreparedRun q k hg front padding S B cost) :
    run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps ≤
      cost + 110 * localBound S cost + 81 := by
  have hpreparation : run.packingSteps + run.arithmeticSteps ≤ cost :=
    run.preparation_time
  have hseed : run.seedSteps ≤ 110 * localBound S cost + 80 := run.seed_time
  omega

private theorem local_visible (command : Cmd 40 896) (a b : Data) (steps S cost : ℕ)
    (he : Eval command steps a b) (ht : steps ≤ cost + 1)
    (ha : ∀ i, ¬H i → (a.stacks i).length ≤ S) :
    ∀ i, ¬H i → (b.stacks i).length ≤ localBound S cost := by
  intro i hi
  have h := trace_selectedStackBits (compiled command 778 777) {i}
    (compiled_trace he 778 777)
  have hh : (b.stacks i).length ≤ (a.stacks i).length + steps := by
    simpa only [selectedStackBits,Finset.sum_singleton] using h
  have := ha i hi
  unfold localBound
  omega

/-- Preparation is polynomial work, so its local step bound controls only
visible growth; untouched caller words contribute a separate maximum. -/
private theorem local_space (command : Cmd 40 896)
    (havoid : ProgramTapeReplay.AvoidsCmd H command) (a b : Data) (steps S cost B : ℕ)
    (he : Eval command steps a b) (ht : steps ≤ cost + 1)
    (ha : ∀ i, ¬H i → (a.stacks i).length ≤ S)
    (hf : ∀ i, H i → (a.stacks i).length ≤ B) :
    StageSpace command (steps + 1) a (max (localBound S cost) B) := by
  have hs := ProgramTapeReplay.eval_rebase H havoid he (fun _ => [])
  constructor
  apply CommandStackTransport.eval_shadow_prefix_bound H havoid
    778 777 hs _ hf
  intro t z htz hz i hi
  have h := trace_selectedStackBits (compiled command 778 777) {i} hz
  have hh : (z.stacks i).length ≤
      ((ProgramTapeReplay.rebaseState H (fun _ => []) a).stacks i).length + t := by
    simpa only [selectedStackBits,Finset.sum_singleton] using h
  have hv : ((ProgramTapeReplay.rebaseState H (fun _ => []) a).stacks i).length ≤ S := by
    simpa only [ProgramTapeReplay.rebaseState,ProgramTapeReplay.rebaseStacks_of_not_mem
      H (fun _ => []) a.stacks i hi] using ha i hi
  by_cases ht' : t ≤ steps
  · unfold localBound
    omega
  · have heq : t = steps + 1 := by omega
    subst t
    have hz' := trace_same_length_unique hz (compiled_halt_trace hs 778 777)
    subst z
    have hb := local_visible command a b steps S cost he ht ha i hi
    change (ProgramTapeReplay.rebaseStacks H (fun _ => []) b.stacks i).length ≤ _
    rw [ProgramTapeReplay.rebaseStacks_of_not_mem H (fun _ => []) b.stacks i hi]
    exact hb

private theorem halt_space {command : Cmd 40 896} {steps bound : ℕ} {a b : Data}
    (he : Eval command steps a b) (hspace : StageSpace command steps a bound) :
    StageSpace command (steps + 1) a bound := by
  constructor
  exact StructuredSpace.compiled_halt_stack_bound he 778 777 hspace.bound

private noncomputable def preparationConstant : ℕ :=
  Classical.choose NativeQueryPreparation.front_resources

private noncomputable def preparationDegree : ℕ :=
  Classical.choose (Classical.choose_spec NativeQueryPreparation.front_resources)

private abbrev preparationResources :=
  Classical.choose_spec (Classical.choose_spec NativeQueryPreparation.front_resources)

private theorem projectedVisible (front : Data) (S : ℕ)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S) :
    ∀ i : Fin 768, ¬LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ S := by
  intro i hi
  apply hvisible (stackMap i)
  intro hh
  simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
  simp only [HighQueryProgram.Carried.words, Finset.mem_insert, Finset.mem_singleton,
    stackMap, Fin.ext_iff, Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hh
  have := i.isLt
  omega

private theorem projectedHidden (front : Data) (S B : ℕ)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B) :
    ∀ i : Fin 768, LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ max S B := by
  intro i _
  by_cases hi : H (stackMap i)
  · exact (hhidden _ hi).trans (Nat.le_max_right _ _)
  · exact (hvisible _ hi).trans (Nat.le_max_left _ _)

private theorem frontRun (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i : Fin 768, ¬LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ S)
    (hhidden : ∀ i : Fin 768, LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ max S B)
    (hvalue : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).val i ≤ S)
    (hlength : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).len i ≤ S)
    (h728 : front.stacks 728 = []) :
    Nonempty (NativeQueryPreparation.FrontRun q k hg (project front) padding S (max S B)
      (preparationConstant * (S + 1) ^ preparationDegree)) :=
  preparationResources q k hg base (project front) padding w S (max S B)
    hfront hvisible hhidden hvalue hlength h728

private theorem finishPreparation (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B)
    (first : MulticolorTypes.Word (preparedProblem q k hg).r (preparedProblem q k hg).Q)
    (rest : List (MulticolorTypes.Word (preparedProblem q k hg).r
      (preparedProblem q k hg).Q)) (packed : Lower) (np na : ℕ)
    (e : LeafRingSetupProgram.Data)
    (M : SubexpPreparedQuartic.Modulus 3 ((preparedModel q k padding).val 33))
    (cache : RingProgram.ScalarCache 3 ((preparedModel q k padding).val 33))
    (half : RingProgram.ScalarCode 3 ((preparedModel q k padding).val 33)) (out : Lower)
    (hrows : (first :: rest).map Subexp.ReadPlan.encodeWord =
      Subexp.AssignmentAlphabetSemantics.wordBytes (preparedProblem q k hg).r
        (preparedProblem q k hg).Q)
    (hnodup : (first :: rest).Nodup) (hcomplete : ∀ z, z ∈ first :: rest)
    (hpack : Eval PackingCallerProgram.command np (project front) packed)
    (hbytes : packed.stacks =
      (PackingCallerProgram.result (project front) (preparedProblem q k hg)
        first rest).stacks)
    (harith : Eval NativeQueryPreparation.arithmeticCommand na packed out)
    (houtput : ArithmeticOutput packed out (preparedModel q k padding)
      (ring_degree_pos (q.input k) padding hg) M cache half e)
    (hdegree : out.stacks 204 =
      List.replicate ((preparedModel q k padding).val 34) true)
    (hinverse : inverseLaw q k hg padding packed M cache half)
    (he : Eval NativeQueryPreparation.command (np + na) (project front) out)
    (htime : np + na ≤ preparationConstant * (S + 1) ^ preparationDegree) :
    Nonempty (PreparedRun q k hg front padding S B
      (preparationConstant * (S + 1) ^ preparationDegree)) := by
  have hp : Eval HighQueryProgram.prepare (np + na + 1) front (result front out) :=
    eval_call_from_state (compiled NativeQueryPreparation.command 700 728) id stackMap front
      Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace he 700 728)
  have hpv := local_visible HighQueryProgram.prepare front (result front out) (np + na + 1) S
    (preparationConstant * (S + 1) ^ preparationDegree) hp (by omega) hvisible
  have hps := local_space HighQueryProgram.prepare HighQueryProgram.Carried.preparation
    front (result front out) (np + na + 1) S
    (preparationConstant * (S + 1) ^ preparationDegree) B hp
    (by omega) hvisible hhidden
  have hpb : ∀ i, ((result front out).stacks i).length ≤
      max (localBound S (preparationConstant * (S + 1) ^ preparationDegree)) B :=
    fun i => hps.bound _ _ (by omega) (compiled_trace hp 778 777) i
  have hmask := HighQueryStart.prepared_mask q k base front padding w packed out
    (packingProblem q k hg) first rest hfront hbytes houtput
  have hseed : ∀ i ∈ HighQueryLocalBounds.seedSources,
      ((result front out).stacks i).length ≤
        localBound S (preparationConstant * (S + 1) ^ preparationDegree) := by
    intro i hi
    apply hpv i
    simp only [HighQueryLocalBounds.seedSources, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hboundary : max (localBound S
      (preparationConstant * (S + 1) ^ preparationDegree)) B ≤
      boundaryBound q S (preparationConstant * (S + 1) ^ preparationDegree) B :=
    Nat.le_max_right _ _
  have hprefix : boundaryBound q S
      (preparationConstant * (S + 1) ^ preparationDegree) B ≤
      prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B :=
    Nat.le_max_right _ _
  obtain ⟨ns, rf, hst, hs, _, hspace, hbound, hcounter, hclear, hguard, hkept⟩ :=
    HighQueryStart.resources q (result front out)
      (localBound S (preparationConstant * (S + 1) ^ preparationDegree))
      (boundaryBound q S (preparationConstant * (S + 1) ^ preparationDegree) B)
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B)
      hmask hseed (Nat.le_max_left _ _) (fun i => (hpb i).trans (hboundary.trans hprefix))
      (Nat.le_max_left _ _) (fun i _ => (hpb i).trans hboundary)
  have hps' : StageSpace HighQueryProgram.prepare (np + na + 1) front
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B) :=
    ⟨fun t z ht hz i => (hps.bound t z (by omega) hz i).trans (hboundary.trans hprefix)⟩
  have hss : StageSpace HighQueryProgram.seed ns (result front out)
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B) :=
    ⟨fun t z ht hz i => hspace t z (by omega) hz i⟩
  have hseq := StageSpace.seq hp hs hps' hss
  have hpseq : Eval (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (np + na + 1 + ns) front (HighCountSeed.initialized (result front out) rf) :=
    hp.seq hs
  have hprefixSpace : StageSpace (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (np + na + 1 + ns + 1) front
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B) := by
    exact halt_space hpseq hseq
  let packingData : PackingData q k hg := {
    first := first
    rest := rest
    packed := packed
    packingSteps := np }
  let arithmeticData : ArithmeticData q k padding := (na, e, M, cache, half, out)
  let seedData : SeedData := {
    seedSteps := ns
    seedRegs := rf }
  let data : PreparedData q k hg padding := (packingData, arithmeticData, seedData)
  let execution : PreparedExecution q k hg front padding data := {
    rows := hrows
    nodup := hnodup
    complete := hcomplete
    packing := hpack
    packed_words := hbytes
    arithmetic := harith
    arithmetic_output := houtput
    degree := hdegree
    inverse := hinverse
    preparation := hp
    seed := hs }
  refine ⟨⟨data, execution, {
    preparation_time := htime
    seed_time := hst
    guard := NativeQueryPreparation.front_guard_register q k base
      (project front) padding w hfront hg
    mask := hmask
    counter := hcounter
    cleared := hclear
    high_guard := hguard
    kept := ?_
    boundary := hbound
    preparation_space := hps'
    seed_space := hss
    prefix_space := hprefixSpace }⟩⟩
  · intro i hi
    exact (hkept i hi).trans
      (HighQueryStart.prepared_kept_frame front packed out (packingProblem q k hg)
        first rest hbytes houtput i hi)

private theorem finishFrontRun (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B)
    (run : NativeQueryPreparation.FrontRun q k hg (project front) padding S (max S B)
      (preparationConstant * (S + 1) ^ preparationDegree)) :
    Nonempty (PreparedRun q k hg front padding S B
      (preparationConstant * (S + 1) ^ preparationDegree)) := by
  rcases run with ⟨data, execution, bounds⟩
  rcases data with ⟨packingData, arithmeticData⟩
  rcases packingData with ⟨first, rest, packed, np⟩
  rcases arithmeticData with ⟨na, e, M, cache, half, out⟩
  rcases execution with ⟨hrows, hnodup, hcomplete, hpack, hbytes, harith, houtput,
    hdegree, hinverse, he⟩
  have htime := bounds.time
  apply finishPreparation q k hg base front padding w S B hfront hvisible hhidden
    first rest packed np na e M cache half out
  all_goals assumption

private theorem prepareSeedFixed (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B)
    (hvalue : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).val i ≤ S)
    (hlength : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).len i ≤ S)
    (h728 : front.stacks 728 = []) :
    Nonempty (PreparedRun q k hg front padding S B
      (preparationConstant * (S + 1) ^ preparationDegree)) := by
  have hv := projectedVisible front S hvisible
  have hh := projectedHidden front S B hvisible hhidden
  obtain ⟨run⟩ := frontRun q k hg base front padding w S B hfront hv hh
    hvalue hlength h728
  exact finishFrontRun q k hg base front padding w S B hfront hvisible hhidden run

/-- The actual prepared run is constructed from the concrete frontend output
and its serialized scalar bounds. Arbitrary suspended caller words affect
only the separate frame bound, never the preparation or seed time. -/
theorem prepare_seed : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
      (base : Lower) (front : Data) (padding : Fin 8 → ℕ) (w : Bank.Words) (S B : ℕ),
      FrontState q k base (project front) padding w →
      (∀ i, ¬H i → (front.stacks i).length ≤ S) →
      (∀ i, H i → (front.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).len i ≤ S) →
      front.stacks 728 = [] → Nonempty (PreparedRun q k hg front padding S B (C*(S+1)^d)) := by
  exact ⟨preparationConstant, preparationDegree, prepareSeedFixed⟩

private theorem hidden_kept (i : Fin 896) (hi : H i) : HashMarkedReturn.kept i = true := by
  simp only [HighQueryProgram.Carried.words,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

/-- Marked setup starts with the actual staged record, executes reference
staging exactly once, constructs the real ring, and initializes the current
high mask. Scalar bounds are on canonical physical frontend lengths. -/
theorem marked : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) (a : Data) (S B : ℕ),
      q.Valid → CleanWork (project a) → Sources q (project a) → q.mark.isSome = true →
      a.stacks 321 = q.index.reverse →
      (∀ i, ¬H i → (a.stacks i).length ≤ S) →
      (∀ i, H i → (a.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ S) →
      let A := S + HighMarkedFrontend.budget q k
      let cost := C * (A+1)^d
      ∃ nf front padding w,
        Eval (HighMarkedFrontend.command k) nf a front ∧
        nf + 1 ≤ HighMarkedFrontend.budget q k ∧
        FrontState q k (markedInput (project a)) (project front) padding w ∧
        ∃ run : PreparedRun q k hg front padding A B cost,
          Eval (.seq (HighMarkedFrontend.command k)
              (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps)) a
            (HighCountSeed.initialized (result front run.output) run.seedRegs) ∧
          nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) ≤
            HighMarkedFrontend.budget q k + cost + 110 * localBound A cost + 81 ∧
          (∀ i, HashMarkedReturn.kept i = true →
            (HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i = a.stacks i) ∧
          StageSpace (.seq (HighMarkedFrontend.command k)
            (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) + 1)
            a (prefixBound q A cost B) := by
  obtain ⟨C,d,hprepare⟩ := prepare_seed
  refine ⟨C,d,?_⟩
  intro q k hg a S B hv hc hs hm href hvisible hhidden hvalue hlength A cost
  obtain ⟨nf,b,_,_,_,he,ht,_⟩ := HighMarkedFrontend.command_eval q k a hv hc hs hm href
  let front := result a b
  have he' : Eval (HighMarkedFrontend.command k) nf a front := he
  obtain ⟨padding,w,hfront⟩ := command_front_state q k a front nf hv hc hs hm href he'
  have hblank := HighFrontendShadow.marked_denominator_empty q k a front nf hv hc hs hm href he'
  have hf := HighMarkedFrontend.command_kept_frame q k a front nf hv hc hs hm href he'
  have hfrontVisible : ∀ i, ¬H i → (front.stacks i).length ≤ A := by
    intro i hi
    have h := trace_selectedStackBits (HighMarkedFrontend.program k) {i}
      (compiled_trace he' 321 338)
    have hh : (front.stacks i).length ≤ (a.stacks i).length + nf := by
      simpa only [selectedStackBits,Finset.sum_singleton] using h
    have := hvisible i hi
    dsimp only [A]
    omega
  have hfrontHidden : ∀ i, H i → (front.stacks i).length ≤ B := by
    intro i hi
    rw [hf i (hidden_kept i hi)]
    exact hhidden i hi
  have hval : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).val i ≤ A := by
    rw [hfront.canonicalLengths]
    exact fun i => (hvalue i).trans (Nat.le_add_right _ _)
  have hlen : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).len i ≤ A := by
    rw [hfront.canonicalLengths]
    exact fun i => (hlength i).trans (Nat.le_add_right _ _)
  obtain ⟨run⟩ := hprepare q k hg (markedInput (project a)) front padding w A B
    hfront hfrontVisible hfrontHidden hval hlen hblank
  have hfrontSpace := local_space (HighMarkedFrontend.command k)
    (HighQueryProgram.Carried.frontend k) a front nf S (HighMarkedFrontend.budget q k) B
    he' (by omega) hvisible hhidden
  have hcap : max (localBound S (HighMarkedFrontend.budget q k)) B ≤ prefixBound q A cost B := by
    apply le_trans _ (Nat.le_max_right _ _)
    apply le_trans _ (Nat.le_max_right _ _)
    apply max_le_max_right
    dsimp [localBound,A]
    omega
  have hfs : StageSpace (HighMarkedFrontend.command k) nf a (prefixBound q A cost B) :=
    ⟨fun t z htz hz i => (hfrontSpace.bound t z (by omega) hz i).trans hcap⟩
  have hrs : StageSpace (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) front
      (prefixBound q A cost B) :=
    ⟨fun t z htz hz i => run.prefix_space.bound t z (Nat.le_succ_of_le htz) hz i⟩
  have hseq := StageSpace.seq he' run.eval hfs hrs
  refine ⟨nf,front,padding,w,he',ht,hfront,run,he'.seq run.eval,?_,?_,?_⟩
  · have hr : run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps ≤
        cost + 110 * localBound A cost + 81 := run.time
    omega
  · intro i hi
    exact (run.kept i hi).trans (hf i hi)
  · exact ⟨StructuredSpace.compiled_halt_stack_bound (he'.seq run.eval) 778 777 hseq.bound⟩

/-- The accepted query executes actual false-flag staging and the same
concrete preparation on history-only sources, retaining the full ambient n. -/
theorem accepted : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) (a : Data) (S B : ℕ),
      q.Valid → CleanWork (project a) → Sources q (project a) → q.mark = none → q.index = [false] →
      (∀ i, ¬H i → (a.stacks i).length ≤ S) →
      (∀ i, H i → (a.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ S) →
      let A := S + HighMarkedFrontend.acceptedBudget q k
      let cost := C * (A+1)^d
      ∃ nf front padding w,
        Eval (HighMarkedFrontend.acceptedCommand k) nf a front ∧
        nf + 1 ≤ HighMarkedFrontend.acceptedBudget q k ∧
        FrontState q k (unmarkedInput (project a)) (project front) padding w ∧
        ∃ run : PreparedRun q k hg front padding A B cost,
          Eval (.seq (HighMarkedFrontend.acceptedCommand k)
              (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps)) a
            (HighCountSeed.initialized (result front run.output) run.seedRegs) ∧
          nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) ≤
            HighMarkedFrontend.acceptedBudget q k + cost + 110 * localBound A cost + 81 ∧
          (∀ i, HashMarkedReturn.kept i = true →
            (HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i = a.stacks i) ∧
          StageSpace (.seq (HighMarkedFrontend.acceptedCommand k)
            (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) + 1)
            a (prefixBound q A cost B) := by
  obtain ⟨C,d,hprepare⟩ := prepare_seed
  refine ⟨C,d,?_⟩
  intro q k hg a S B hv hc hs hm hindex hvisible hhidden hvalue hlength A cost
  obtain ⟨nf,b,_,_,_,he,ht,_⟩ := HighMarkedFrontend.accepted_command_eval q k a hv hc hs hm hindex
  let front := result a b
  have he' : Eval (HighMarkedFrontend.acceptedCommand k) nf a front := he
  obtain ⟨padding,w,hfront⟩ := accepted_command_front_state q k a front nf hv hc hs hm hindex he'
  have hblank := HighFrontendShadow.accepted_denominator_empty q k a front nf hv hc hs hm hindex he'
  have hf := HighMarkedFrontend.accepted_command_kept_frame q k a front nf hv hc hs hm hindex he'
  have hfrontVisible : ∀ i, ¬H i → (front.stacks i).length ≤ A := by
    intro i hi
    have h := trace_selectedStackBits (HighMarkedFrontend.acceptedProgram k) {i}
      (compiled_trace he' 700 338)
    have hh : (front.stacks i).length ≤ (a.stacks i).length + nf := by
      simpa only [selectedStackBits,Finset.sum_singleton] using h
    have := hvisible i hi
    dsimp only [A]
    omega
  have hfrontHidden : ∀ i, H i → (front.stacks i).length ≤ B := by
    intro i hi
    rw [hf i (hidden_kept i hi)]
    exact hhidden i hi
  have hval : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).val i ≤ A := by
    rw [hfront.canonicalLengths]
    exact fun i => (hvalue i).trans (Nat.le_add_right _ _)
  have hlen : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).len i ≤ A := by
    rw [hfront.canonicalLengths]
    exact fun i => (hlength i).trans (Nat.le_add_right _ _)
  obtain ⟨run⟩ := hprepare q k hg (unmarkedInput (project a)) front padding w A B
    hfront hfrontVisible hfrontHidden hval hlen hblank
  have hfrontSpace := local_space (HighMarkedFrontend.acceptedCommand k)
    (HighQueryProgram.Carried.accepted_frontend k) a front nf S (HighMarkedFrontend.acceptedBudget q k) B
    he' (by omega) hvisible hhidden
  have hcap : max (localBound S (HighMarkedFrontend.acceptedBudget q k)) B ≤ prefixBound q A cost B := by
    apply le_trans _ (Nat.le_max_right _ _)
    apply le_trans _ (Nat.le_max_right _ _)
    apply max_le_max_right
    dsimp [localBound,A]
    omega
  have hfs : StageSpace (HighMarkedFrontend.acceptedCommand k) nf a (prefixBound q A cost B) :=
    ⟨fun t z htz hz i => (hfrontSpace.bound t z (by omega) hz i).trans hcap⟩
  have hrs : StageSpace (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) front
      (prefixBound q A cost B) :=
    ⟨fun t z htz hz i => run.prefix_space.bound t z (Nat.le_succ_of_le htz) hz i⟩
  have hseq := StageSpace.seq he' run.eval hfs hrs
  refine ⟨nf,front,padding,w,he',ht,hfront,run,he'.seq run.eval,?_,?_,?_⟩
  · have hr : run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps ≤
        cost + 110 * localBound A cost + 81 := run.time
    omega
  · intro i hi
    exact (run.kept i hi).trans (hf i hi)
  · exact ⟨StructuredSpace.compiled_halt_stack_bound (he'.seq run.eval) 778 777 hseq.bound⟩

/-- The actual guard is tested at the frontend output before preparation.
An actual high-loop continuation therefore installs into the original fixed
syntax, paying the conditional microstep once. -/
theorem PreparedRun.guard_loop {q k hg front padding S B cost}
    (run : PreparedRun q k hg front padding S B cost) (last : Data) (steps K : ℕ)
    (hloop : Eval HighQueryProgram.highLoop steps
      (HighCountSeed.initialized (result front run.output) run.seedRegs) last)
    (hspace : StageSpace HighQueryProgram.highLoop steps
      (HighCountSeed.initialized (result front run.output) run.seedRegs) K) :
    Eval HighQueryProgram.guardedCount
      (run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + steps) + 1) front last ∧
      StageSpace HighQueryProgram.guardedCount
        (run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + steps) + 2) front
        (max (prefixBound q S cost B) K) := by
  have hp : StageSpace HighQueryProgram.prepare (run.packingSteps+run.arithmeticSteps+1)
      front (max (prefixBound q S cost B) K) :=
    ⟨fun t z ht hz i => (run.preparation_space.bound t z ht hz i).trans (Nat.le_max_left _ _)⟩
  have hs : StageSpace HighQueryProgram.seed run.seedSteps (result front run.output)
      (max (prefixBound q S cost B) K) :=
    ⟨fun t z ht hz i => (run.seed_space.bound t z ht hz i).trans (Nat.le_max_left _ _)⟩
  have hl : StageSpace HighQueryProgram.highLoop steps
      (HighCountSeed.initialized (result front run.output) run.seedRegs)
      (max (prefixBound q S cost B) K) :=
    ⟨fun t z ht hz i => (hspace.bound t z ht hz i).trans (Nat.le_max_right _ _)⟩
  have he : Eval HighQueryProgram.preparedCount
      (run.packingSteps+run.arithmeticSteps+1+(run.seedSteps+steps)) front last :=
    run.preparation.seq (run.seed.seq hloop)
  have hpref := StageSpace.seq run.preparation (run.seed.seq hloop) hp
    (StageSpace.seq run.seed hloop hs hl)
  have hcond := HighQueryProgram.guardedCount_true_eval front last _ run.guard he
  have hc := StructuredSpace.conditional_true_stack_bound (no:=HighQueryProgram.reject)
    run.guard he 778 777 hpref.bound _ _ _
    (compiled_site HighQueryProgram.guardedCount 778 777)
  exact ⟨hcond,⟨StructuredSpace.compiled_halt_stack_bound hcond 778 777 hc⟩⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
