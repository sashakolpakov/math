import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseMastersProgram
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryFamily
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds

namespace OAI.Algorithms

/-!
# Actual entry preparation for the paired clause-family program

The five retained inputs are binary n, binary ell, the prime word, binary D,
and the forward encoded leaf. The fixed code constructs the unary-factor
prefix, saves both streams, builds the clause shape masters, and copies the
leaf. No scope list, factor table, or unary shape is supplied as an oracle.
-/

namespace SubexponentialSAT.SubexpLayoutRawPreparation

open BitProgram StructuredCalls SubexpSetupStorage

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 16 45
abbrev Code := Cmd 16 45

structure Inputs where
  counts : SubexpClauseMastersProgram.Inputs
  leaf : List Bool

def inputState (regs : Fin 16 → Bool) (x : Inputs) : Data :=
  ⟨regs, fun i => if i.val = 35 then x.counts.n else
    if i.val = 36 then x.counts.ell else if i.val = 37 then x.counts.modulus else
    if i.val = 38 then x.counts.dimension else if i.val = 39 then x.leaf else []⟩

def temporary : Fin 45 := 44
def unaryPort (i : Fin 20) : Fin 45 := i.castAdd 25
def unaryWork : List (Fin 45) := List.ofFn unaryPort
def unaryInputs : List (Fin 45 × Fin 45) := [(35, 1), (36, 3), (37, 16)]
def unaryOutputs : List (Fin 45 × Fin 45) := [(0, 32), (19, 33)]

theorem unaryPort_injective : Function.Injective unaryPort := Fin.castAdd_injective 20 25

@[simp] theorem mem_unaryWork (i : Fin 45) : i ∈ unaryWork ↔ i.val < 20 := by
  simp only [unaryWork, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩; exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem unary_inputs_good : ∀ q ∈ unaryInputs,
    q.1 ≠ q.2 ∧ q.1 ≠ temporary ∧ temporary ≠ q.2 := by
  intro q h
  simp only [unaryInputs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

theorem unary_outputs_good : ∀ q ∈ unaryOutputs,
    q.1 ≠ q.2 ∧ q.1 ≠ temporary ∧ temporary ≠ q.2 := by
  intro q h
  simp only [unaryOutputs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

theorem unary_outputs_separated : ∀ q ∈ unaryOutputs, ∀ z ∈ unaryOutputs,
    q.1 ≠ z.2 := by
  intro q h z hz
  simp only [unaryOutputs, List.mem_cons, List.not_mem_nil, or_false] at h hz
  rcases h with rfl | rfl <;> rcases hz with rfl | rfl <;> decide

def seed (a : Data) : Data := prepareState temporary unaryWork unaryInputs a

theorem seed_entry (regs : Fin 16 → Bool) (x : Inputs) :
    project id unaryPort (seed (inputState regs x)) =
      SubexpUnaryFamily.initialState
        (seed (inputState regs x)).regs x.counts.n x.counts.ell x.counts.modulus := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp [ seed, prepareState, beforeCopies, resetMany_stacks,
        clearMany_stacks, copyManyState, copyState, StackRoutines.copyStacks,
        unaryInputs, unaryPort, inputState, temporary]

theorem seed_high_frame (a : Data) (i : Fin 45) (hi : 20 ≤ i.val)
    (ht : i ≠ temporary) : (seed a).stacks i = a.stacks i := by
  apply prepare_frame temporary unaryWork unaryInputs a i ht
  · simpa only [mem_unaryWork] using (Nat.not_lt.mpr hi)
  · intro q hq
    simp only [unaryInputs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> intro h <;>
      have hv := congrArg Fin.val h <;> norm_num at hv <;> omega

noncomputable def middle (a : Data) (u : State 16 20) : Data :=
  embedState id unaryPort (seed a) u

theorem middle_high_frame (a : Data) (u : State 16 20) (i : Fin 45)
    (hi : 20 ≤ i.val) (ht : i ≠ temporary) :
    (middle a u).stacks i = a.stacks i := by
  unfold middle
  rw [embedState_stack_frame id unaryPort (seed a) u i (by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega)]
  exact seed_high_frame a i hi ht

noncomputable def prefixed (a : Data) (u : State 16 20) : Data :=
  finishState unaryWork unaryOutputs (middle a u)

def unaryStage : Code :=
  isolated SubexpUnaryFamily.program id unaryPort temporary unaryWork unaryInputs unaryOutputs

theorem unaryStage_eval (regs : Fin 16 → Bool) (x : Inputs)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hwidth : CounterPrograms.value x.counts.ell ≤ x.counts.modulus.length) :
    ∃ (t : ℕ) (u : State 16 20),
      t ≤ SubexpUnaryFamily.runtimeBound x.counts.n x.counts.ell x.counts.modulus ∧
      u.stacks 0 = Encoding.encodeList id (SubexpUnaryFamily.chunkTables
        (CounterPrograms.value x.counts.n) (CounterPrograms.value x.counts.ell)
        x.counts.modulus) ∧
      u.stacks 19 = SubexpChunkDescriptorEncoding.scopes 0
        (ChunkPartition.count (CounterPrograms.value x.counts.n)
          (CounterPrograms.value x.counts.ell)) ∧
      RunsIn SubexpUnaryFamily.program
        (SubexpUnaryFamily.runtimeBound x.counts.n x.counts.ell x.counts.modulus)
        ((SubexpUnaryFamily.initialState (seed (inputState regs x)).regs
          x.counts.n x.counts.ell x.counts.modulus).withPC
            (some SubexpUnaryFamily.program.entry)) (u.withPC none) ∧
      Eval unaryStage
        (prepareCost temporary unaryWork unaryInputs (inputState regs x) +
          (t + finishCost unaryWork unaryOutputs (middle (inputState regs x) u)))
        (inputState regs x) (prefixed (inputState regs x) u) := by
  obtain ⟨u, _, _, hs, ht, t, hb, he⟩ := SubexpUnaryFamily.program_runsIn
    (seed (inputState regs x)).regs x.counts.n x.counts.ell x.counts.modulus hell hwidth
  have htrace : Trace SubexpUnaryFamily.program t
      ((project id unaryPort (seed (inputState regs x))).withPC
        (some SubexpUnaryFamily.program.entry)) (u.withPC none) := by
    simpa only [seed_entry] using he
  refine ⟨t, u, hb, ht, hs, ⟨t, hb, he⟩, ?_⟩
  exact isolated_eval SubexpUnaryFamily.program id unaryPort Function.injective_id
    unaryPort_injective temporary unaryWork unaryInputs unaryOutputs (inputState regs x) u
    unary_inputs_good unary_outputs_good (by
      rintro ⟨i, h⟩
      have hv := congrArg Fin.val h
      change i.val = 44 at hv
      omega) htrace

theorem prefixed_low (a : Data) (u : State 16 20) (i : Fin 45) (hi : i.val < 20) :
    (prefixed a u).stacks i = [] :=
  finish_empty unaryWork unaryOutputs (middle a u) i ((mem_unaryWork i).mpr hi)

theorem prefixed_tables (a : Data) (u : State 16 20) :
    (prefixed a u).stacks 32 = u.stacks 0 := by
  have h := finish_value unaryWork unaryOutputs (middle a u)
    (by decide) unary_outputs_separated (0, 32) (by simp [unaryOutputs])
    (by simp only [mem_unaryWork]; decide)
  exact h.trans (embedState_stack id unaryPort (seed a) u unaryPort_injective 0)

theorem prefixed_scopes (a : Data) (u : State 16 20) :
    (prefixed a u).stacks 33 = u.stacks 19 := by
  have h := finish_value unaryWork unaryOutputs (middle a u)
    (by decide) unary_outputs_separated (19, 33) (by simp [unaryOutputs])
    (by simp only [mem_unaryWork]; decide)
  exact h.trans (embedState_stack id unaryPort (seed a) u unaryPort_injective 19)

theorem prefixed_high_frame (a : Data) (u : State 16 20) (i : Fin 45)
    (hi : 20 ≤ i.val) (h32 : i ≠ 32) (h33 : i ≠ 33) (ht : i ≠ temporary) :
    (prefixed a u).stacks i = a.stacks i := by
  unfold prefixed
  rw [finish_frame unaryWork unaryOutputs (middle a u) i
    (by simpa only [mem_unaryWork] using (Nat.not_lt.mpr hi)) (by
      intro q hq
      simp only [unaryOutputs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h32
      · exact h33)]
  exact middle_high_frame a u i hi ht

theorem prefixed_temporary (a : Data) (u : State 16 20) :
    (prefixed a u).stacks temporary = [] := by
  unfold prefixed
  rw [finish_frame unaryWork unaryOutputs (middle a u) temporary
    (by simp only [mem_unaryWork]; decide) (by
      intro q hq
      simp only [unaryOutputs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> decide)]
  unfold middle
  rw [embedState_stack_frame id unaryPort (seed a) u temporary (by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val = 44 at hv
    omega)]
  exact prepare_temporary temporary unaryWork unaryInputs a unary_inputs_good

def masterRegister (i : Fin 3) : Fin 16 := i.castAdd 13
def masterPort : Fin 14 → Fin 45 := ![35, 36, 37, 38, 21, 23, 22, 26, 30, 18, 40, 41, 42, 43]

theorem masterRegister_injective : Function.Injective masterRegister := Fin.castAdd_injective 3 13
theorem masterPort_injective : Function.Injective masterPort := by decide

theorem prefixed_entry (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) :
    project masterRegister masterPort (prefixed (inputState regs x) u) =
      SubexpClauseMastersProgram.initialState
        ((prefixed (inputState regs x) u).regs ∘ masterRegister) x.counts := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i
    all_goals change (prefixed (inputState regs x) u).stacks _ = _
    all_goals first
      | rw [prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]; rfl
      | exact prefixed_low _ _ _ (by decide)

def masterStage : Code :=
  invoke SubexpClauseMastersProgram.program masterRegister masterPort

noncomputable def mastered (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) : Data :=
  embedState masterRegister masterPort (prefixed (inputState regs x) u)
    (SubexpClauseMastersProgram.outputState x.counts)

theorem masterStage_eval (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) :
    ∃ t ≤ SubexpClauseMastersProgram.workBound x.counts + 1,
      Eval masterStage t (prefixed (inputState regs x) u) (mastered regs x u) := by
  obtain ⟨t, ht, he⟩ := SubexpClauseMastersProgram.runs
    ((prefixed (inputState regs x) u).regs ∘ masterRegister) x.counts
  refine ⟨t, ht, ?_⟩
  apply invoke_eval SubexpClauseMastersProgram.program masterRegister masterPort
    masterRegister_injective masterPort_injective
  simpa only [prefixed_entry] using he

theorem mastered_at (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) (i : Fin 14) :
    (mastered regs x u).stacks (masterPort i) =
      (SubexpClauseMastersProgram.outputState x.counts).stacks i :=
  embedState_stack masterRegister masterPort (prefixed (inputState regs x) u)
    (SubexpClauseMastersProgram.outputState x.counts) masterPort_injective i

theorem mastered_frame (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20)
    (i : Fin 45) (hi : ¬ ∃ j, masterPort j = i) :
    (mastered regs x u).stacks i = (prefixed (inputState regs x) u).stacks i :=
  embedState_stack_frame masterRegister masterPort (prefixed (inputState regs x) u)
    (SubexpClauseMastersProgram.outputState x.counts) i hi

theorem mastered_leaf (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) :
    (mastered regs x u).stacks 39 = x.leaf := by
  rw [mastered_frame _ _ _ _ (by decide),
    prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem mastered_temporary (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) :
    (mastered regs x u).stacks temporary = [] := by
  rw [mastered_frame _ _ _ _ (by decide)]
  exact prefixed_temporary _ _

def command : Code := .seq unaryStage (.seq masterStage
  (.seq (copyCmd 39 31 temporary) RegisterResetProgram.all))

abbrev program : Program 16 45 (size command + 1) := compiled command 39 32

noncomputable def result (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) : Data :=
  RegisterResetProgram.zeroed (copyState 39 31 (mastered regs x u))

def outputStacks (x : Inputs) (tables scopes : List Bool) (i : Fin 45) : List Bool :=
  if i.val = 18 then x.counts.modulus else
  if i.val = 21 then SubexpClauseMastersProgram.unary x.counts.n else
  if i.val = 22 then SubexpFullShapeProgram.fullShape
    (CounterPrograms.value x.counts.dimension) (SubexpClauseMastersProgram.unary x.counts.ell) else
  if i.val = 23 then SubexpClauseMastersProgram.unary x.counts.ell else
  if i.val = 26 then x.counts.modulus else if i.val = 30 then x.counts.ell else
  if i.val = 31 then x.leaf else if i.val = 32 then tables else
  if i.val = 33 then scopes else (inputState (fun _ => false) x).stacks i

def outputState (x : Inputs) (tables scopes : List Bool) : Data :=
  ⟨fun _ => false, outputStacks x tables scopes⟩

theorem result_eq (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20) :
    result regs x u = outputState x (u.stacks 0) (u.stacks 19) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change (copyState 39 31 (mastered regs x u)).stacks i =
      outputStacks x (u.stacks 0) (u.stacks 19) i
    fin_cases i
    · change (mastered regs x u).stacks 0 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 1 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 2 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 3 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 4 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 5 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 6 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 7 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 8 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 9 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 10 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 11 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 12 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 13 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 14 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 15 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 16 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 17 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · exact mastered_at regs x u 9
    · change (mastered regs x u).stacks 19 = []
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_low _ _ _ (by decide)
    · change (mastered regs x u).stacks 20 = []
      rw [mastered_frame _ _ _ _ (by decide),
        prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · exact mastered_at regs x u 4
    · exact mastered_at regs x u 6
    · exact mastered_at regs x u 5
    · change (mastered regs x u).stacks 24 = []
      rw [mastered_frame _ _ _ _ (by decide),
        prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · change (mastered regs x u).stacks 25 = []
      rw [mastered_frame _ _ _ _ (by decide),
        prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · exact mastered_at regs x u 7
    · change (mastered regs x u).stacks 27 = []
      rw [mastered_frame _ _ _ _ (by decide),
        prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · change (mastered regs x u).stacks 28 = []
      rw [mastered_frame _ _ _ _ (by decide),
        prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · change (mastered regs x u).stacks 29 = []
      rw [mastered_frame _ _ _ _ (by decide),
        prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · exact mastered_at regs x u 8
    · change (mastered regs x u).stacks 39 ++ (mastered regs x u).stacks 31 = x.leaf
      rw [mastered_leaf, mastered_frame _ _ _ 31 (by decide),
        prefixed_high_frame _ _ 31 (by decide) (by decide) (by decide) (by decide)]
      exact List.append_nil _
    · change (mastered regs x u).stacks 32 = u.stacks 0
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_tables _ _
    · change (mastered regs x u).stacks 33 = u.stacks 19
      rw [mastered_frame _ _ _ _ (by decide)]
      exact prefixed_scopes _ _
    · change (mastered regs x u).stacks 34 = []
      rw [mastered_frame _ _ _ _ (by decide),
        prefixed_high_frame _ _ _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · exact mastered_at regs x u 0
    · exact mastered_at regs x u 1
    · exact mastered_at regs x u 2
    · exact mastered_at regs x u 3
    · exact mastered_leaf regs x u
    · exact mastered_at regs x u 10
    · exact mastered_at regs x u 11
    · exact mastered_at regs x u 12
    · exact mastered_at regs x u 13
    · exact mastered_temporary regs x u
def inputMass (x : Inputs) : ℕ := x.counts.n.length + x.counts.ell.length +
  x.counts.modulus.length + x.counts.dimension.length + x.leaf.length

theorem input_bound (regs : Fin 16 → Bool) (x : Inputs) :
    SubexpPreparedSetupCalls.StackBound (inputState regs x) (inputMass x) := by
  intro i
  simp only [inputState]
  split_ifs <;> dsimp [inputMass] <;> omega

theorem seed_bound (regs : Fin 16 → Bool) (x : Inputs) :
    SubexpPreparedSetupCalls.StackBound (seed (inputState regs x)) (inputMass x) := by
  unfold seed prepareState
  apply SubexpPreparedSetupCalls.copyMany_bound
    unaryInputs _ (SubexpPreparedSetupCalls.beforeCopies_bound _ _ _ (input_bound regs x))
  · decide
  · intro q hq
    simp only [unaryInputs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      simp [beforeCopies, resetMany_stacks, clearMany_stacks]
  · intro q hq z hz
    simp only [unaryInputs, List.mem_cons, List.not_mem_nil, or_false] at hq hz
    rcases hq with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;> decide

theorem prepareCost_bound (regs : Fin 16 → Bool) (x : Inputs) :
    prepareCost temporary unaryWork unaryInputs (inputState regs x) ≤
      100 * (inputMass x + 1) := by
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le [temporary]
    (inputState regs x) (input_bound regs x)
  have h2 := SubexpPreparedSetupCalls.clearManyCost_le unaryWork
    (clearManyState [temporary] (inputState regs x))
    (SubexpPreparedSetupCalls.clearMany_bound _ _ (input_bound regs x))
  have h3 := SubexpPreparedSetupCalls.copyManyCost_le unaryInputs
    (beforeCopies temporary unaryWork (inputState regs x))
    (fun q _ => SubexpPreparedSetupCalls.beforeCopies_bound _ _ _ (input_bound regs x) q.1)
    (by
      intro q hq z hz
      simp only [unaryInputs, List.mem_cons, List.not_mem_nil, or_false] at hq hz
      rcases hq with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;> decide)
  have hlen : unaryWork.length = 20 := by simp [unaryWork]
  have hin : unaryInputs.length = 3 := rfl
  simp only [List.length_singleton, one_mul] at h1
  rw [hlen] at h2
  rw [hin] at h3
  unfold prepareCost
  omega

theorem finishCost_bound (a : Data) {W : ℕ}
    (ha : SubexpPreparedSetupCalls.StackBound a W) :
    finishCost unaryWork unaryOutputs a ≤ 100 * (W + 1) := by
  let b := clearManyState (unaryOutputs.map Prod.snd) a
  have hb : SubexpPreparedSetupCalls.StackBound b W :=
    SubexpPreparedSetupCalls.clearMany_bound _ a ha
  have hc : SubexpPreparedSetupCalls.StackBound (copyManyState unaryOutputs b) W := by
    apply SubexpPreparedSetupCalls.copyMany_bound _ b hb
    · decide
    · intro q hq
      dsimp [b]
      rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
    · exact unary_outputs_separated
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le (unaryOutputs.map Prod.snd) a ha
  have h2 := SubexpPreparedSetupCalls.copyManyCost_le unaryOutputs b
    (fun q _ => hb q.1) unary_outputs_separated
  have h3 := SubexpPreparedSetupCalls.clearManyCost_le unaryWork _ hc
  have hout : unaryOutputs.length = 2 := rfl
  have hlen : unaryWork.length = 20 := by simp [unaryWork]
  rw [List.length_map, hout] at h1
  rw [hout] at h2
  rw [hlen] at h3
  change _ + (_ + (_ + 9)) ≤ _
  change clearManyCost (unaryOutputs.map Prod.snd) a +
    (copyManyCost unaryOutputs b + (clearManyCost unaryWork (copyManyState unaryOutputs b) + 9)) ≤ _
  omega

theorem middle_bound (regs : Fin 16 → Bool) (x : Inputs) (u : State 16 20)
    (hrun : RunsIn SubexpUnaryFamily.program
      (SubexpUnaryFamily.runtimeBound x.counts.n x.counts.ell x.counts.modulus)
      ((SubexpUnaryFamily.initialState (seed (inputState regs x)).regs
        x.counts.n x.counts.ell x.counts.modulus).withPC
          (some SubexpUnaryFamily.program.entry)) (u.withPC none)) :
    SubexpPreparedSetupCalls.StackBound (middle (inputState regs x) u)
      (20 * inputMass x + SubexpUnaryFamily.runtimeBound
        x.counts.n x.counts.ell x.counts.modulus) := by
  let initial := SubexpUnaryFamily.initialState (seed (inputState regs x)).regs
    x.counts.n x.counts.ell x.counts.modulus
  have hi : ∀ i : Fin 20, (initial.stacks i).length ≤ inputMass x := by
    intro i
    simp only [initial, SubexpUnaryFamily.initialState]
    split_ifs <;> dsimp [inputMass] <;> omega
  have his : BitProgram.stackBits initial.stacks ≤ 20 * inputMass x := by
    have hh := Finset.sum_le_sum (fun (i : Fin 20) (_ : i ∈ Finset.univ) => hi i)
    calc
      BitProgram.stackBits initial.stacks ≤ ∑ _ : Fin 20, inputMass x := hh
      _ = 20 * inputMass x := by simp
  have hu := BitProgram.runsIn_dataBits SubexpUnaryFamily.program hrun
  change BitProgram.stackBits u.stacks ≤ BitProgram.stackBits initial.stacks + _ at hu
  have hub (i : Fin 20) : (u.stacks i).length ≤ 20 * inputMass x +
      SubexpUnaryFamily.runtimeBound x.counts.n x.counts.ell x.counts.modulus := by
    have hs : (u.stacks i).length ≤ BitProgram.stackBits u.stacks := by
      change (u.stacks i).length ≤ Finset.sum Finset.univ (fun j : Fin 20 => (u.stacks j).length)
      exact Finset.single_le_sum (fun (j : Fin 20) _ => Nat.zero_le (u.stacks j).length)
        (Finset.mem_univ i)
    omega
  intro i
  by_cases hm : ∃ j, unaryPort j = i
  · obtain ⟨j, rfl⟩ := hm
    unfold middle
    rw [embedState_stack id unaryPort _ u unaryPort_injective]
    exact hub j
  · unfold middle
    rw [embedState_stack_frame id unaryPort _ u i hm]
    have h := seed_bound regs x i
    omega

def runtimeBound (x : Inputs) : ℕ := 5000 * (inputMass x +
  SubexpUnaryFamily.runtimeBound x.counts.n x.counts.ell x.counts.modulus +
  SubexpClauseMastersProgram.workBound x.counts + 1)

theorem command_execution (regs : Fin 16 → Bool) (x : Inputs)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hwidth : CounterPrograms.value x.counts.ell ≤ x.counts.modulus.length) :
    ∃ n ≤ runtimeBound x,
      Eval command n (inputState regs x)
        (outputState x (Encoding.encodeList id (SubexpUnaryFamily.chunkTables
          (CounterPrograms.value x.counts.n) (CounterPrograms.value x.counts.ell)
          x.counts.modulus)) (SubexpChunkDescriptorEncoding.scopes 0
            (ChunkPartition.count (CounterPrograms.value x.counts.n)
              (CounterPrograms.value x.counts.ell)))) := by
  obtain ⟨tu, u, htu, hu0, hu19, huRun, hu⟩ := unaryStage_eval regs x hell hwidth
  obtain ⟨tm, htm, hm⟩ := masterStage_eval regs x u
  have hc := copy_eval (39 : Fin 45) 31 temporary (mastered regs x u)
    (by decide) (by decide) (by decide) (mastered_temporary regs x u)
  rw [mastered_leaf] at hc
  have hz := RegisterResetProgram.all_eval (copyState 39 31 (mastered regs x u))
  have he := hu.seq (hm.seq (hc.seq hz))
  change Eval command _ (inputState regs x) (result regs x u) at he
  rw [result_eq, hu0, hu19] at he
  refine ⟨_, ?_, he⟩
  have hprep := prepareCost_bound regs x
  have hfinish := finishCost_bound (middle (inputState regs x) u) (middle_bound regs x u huRun)
  have hleaf : x.leaf.length ≤ inputMass x := by dsimp [inputMass]; omega
  unfold runtimeBound
  omega

theorem program_runs (regs : Fin 16 → Bool) (x : Inputs)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hwidth : CounterPrograms.value x.counts.ell ≤ x.counts.modulus.length) :
    RunsIn program (runtimeBound x + 1)
      ((inputState regs x).withPC (some program.entry))
      ((outputState x (Encoding.encodeList id (SubexpUnaryFamily.chunkTables
        (CounterPrograms.value x.counts.n) (CounterPrograms.value x.counts.ell)
        x.counts.modulus)) (SubexpChunkDescriptorEncoding.scopes 0
          (ChunkPartition.count (CounterPrograms.value x.counts.n)
            (CounterPrograms.value x.counts.ell)))).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_execution regs x hell hwidth
  exact ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 39 32⟩

end SubexponentialSAT.SubexpLayoutRawPreparation

end OAI.Algorithms
