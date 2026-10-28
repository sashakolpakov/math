import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutRawPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpClauseFamilyProgram

namespace OAI.Algorithms

/-!
# Concrete raw factor construction for the layout phase

The fixed program constructs the unary-factor prefix, its shape masters, and
all clause factors in encounter order. The paired family mapper performs the
actual concatenation. The same resulting scope stream feeds assignment and
the same table stream feeds the later source builder.
-/

namespace SubexponentialSAT.SubexpLayoutConstruction

open BitProgram StructuredCalls

abbrev Data := SubexpLayoutRawPreparation.Data
abbrev Inputs := SubexpLayoutRawPreparation.Inputs

def dimension (x : Inputs) : ℕ := CounterPrograms.value x.counts.dimension
def variableCount (x : Inputs) : ℕ := CounterPrograms.value x.counts.n

def familyInputs (x : Inputs) : SubexpClauseFamilyProgram.Inputs where
  modulus := x.counts.modulus
  nShape := SubexpClauseMastersProgram.unary x.counts.n
  fullShape := SubexpFullShapeProgram.fullShape (dimension x)
    (SubexpClauseMastersProgram.unary x.counts.ell)
  ellShape := SubexpClauseMastersProgram.unary x.counts.ell
  clause := []
  widthShape := x.counts.modulus
  binaryEll := x.counts.ell

def prefixTables (x : Inputs) : List (List Bool) :=
  SubexpUnaryFamily.chunkTables (variableCount x)
    (CounterPrograms.value x.counts.ell) x.counts.modulus

def prefixScopes (x : Inputs) : List (List Bool) :=
  ((List.range' 0 (ChunkPartition.count (variableCount x)
    (CounterPrograms.value x.counts.ell))).map List.singleton).map
      (Encoding.encodeList Encoding.encodeNat)

theorem encodeList_map {α : Type} (f : α → List Bool) (xs : List α) :
    Encoding.encodeList id (xs.map f) = Encoding.encodeList f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

theorem prefixScopes_encoded (x : Inputs) :
    Encoding.encodeList id (prefixScopes x) = SubexpChunkDescriptorEncoding.scopes 0
      (ChunkPartition.count (variableCount x) (CounterPrograms.value x.counts.ell)) := by
  exact encodeList_map _ _

def prepared (x : Inputs) : Data :=
  SubexpLayoutRawPreparation.outputState x
    (Encoding.encodeList id (prefixTables x)) (Encoding.encodeList id (prefixScopes x))

def familyRegister (i : Fin 14) : Fin 16 := i.castAdd 2
def familyPort (i : Fin 35) : Fin 45 := i.castAdd 10

theorem familyRegister_injective : Function.Injective familyRegister :=
  Fin.castAdd_injective 14 2
theorem familyPort_injective : Function.Injective familyPort := Fin.castAdd_injective 35 10

def projectFamily (a : Data) : SubexpClauseFamilySupport.Data :=
  projectState familyRegister familyPort a

theorem prepared_ready (x : Inputs) :
    SubexpClauseFamilyProgram.Ready (familyInputs x) (projectFamily (prepared x)) := by
  intro i
  fin_cases i <;> rfl

theorem family_valid (x : Inputs)
    (hp : 0 < BinaryArithmetic.toNat x.counts.modulus)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hwidth : CounterPrograms.value x.counts.ell ≤ x.counts.modulus.length)
    (hD : dimension x = ChunkPartition.count (variableCount x)
      (CounterPrograms.value x.counts.ell)) :
    SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x) := by
  refine ⟨hp, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [familyInputs, CounterPrograms.value_eq_toNat] using hell
  · simp [familyInputs, SubexpClauseMastersProgram.unary, CounterPrograms.value_eq_toNat]
  · simpa only [familyInputs, SubexpClauseMastersProgram.unary, List.length_replicate] using hwidth
  · simp [familyInputs, SubexpClauseMastersProgram.unary]
  · simp [familyInputs, SubexpClauseMastersProgram.unary, variableCount]
  · exact (SubexpClauseMastersProgram.output_covers x.counts hell hD).1

abbrev familyCall : Cmd 16 45 := .call
  (ProgramLinking.liftProgram SubexpClauseFamilyProgram.program familyRegister familyPort)

abbrev command : Cmd 16 45 := .seq (.call SubexpLayoutRawPreparation.program) familyCall
abbrev program : Program 16 45 (size command + 1) := compiled command 39 32

def tables (x : Inputs) (hv : SubexpClauseFamilyProgram.Valid (familyInputs x)
    (dimension x) (variableCount x))
    (clauses : List (List (SAT.Literal (Fin (variableCount x))))) : List (List Bool) :=
  prefixTables x ++ SubexpClauseFamilyProgram.tables (familyInputs x) hv clauses

def scopes (x : Inputs)
    (clauses : List (List (SAT.Literal (Fin (variableCount x))))) : List (List Bool) :=
  prefixScopes x ++ SubexpClauseFamilyProgram.scopes (familyInputs x) clauses

def runtimeBound (x : Inputs) (hv : SubexpClauseFamilyProgram.Valid (familyInputs x)
    (dimension x) (variableCount x))
    (clauses : List (List (SAT.Literal (Fin (variableCount x))))) : ℕ :=
  SubexpLayoutRawPreparation.runtimeBound x +
    SubexpClauseFamilyProgram.budget (familyInputs x) hv clauses (prefixTables x) (prefixScopes x) + 3

/-- Both streams arise from the actual fixed programs, and the retained raw
input and scalar words survive the complete construction. -/
theorem program_runs (regs : Fin 16 → Bool) (x : Inputs)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hwidth : CounterPrograms.value x.counts.ell ≤ x.counts.modulus.length)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (clauses : List (List (SAT.Literal (Fin (variableCount x)))))
    (hsource : x.leaf = Encoding.encodeList SubexpClauseRowProgram.clauseBytes clauses) :
    ∃ out : Data,
      RunsIn program (runtimeBound x hv clauses)
        ((SubexpLayoutRawPreparation.inputState regs x).withPC (some program.entry))
        (out.withPC none) ∧
      out.stacks 32 = Encoding.encodeList id (tables x hv clauses) ∧
      out.stacks 33 = Encoding.encodeList id (scopes x clauses) ∧
      out.stacks 31 = [] ∧ out.stacks 34 = [] ∧
      SubexpClauseFamilyProgram.Ready (familyInputs x) (projectFamily out) ∧
      (∀ i : Fin 45, 35 ≤ i.val → out.stacks i = (prepared x).stacks i) := by
  have hp : RunsIn SubexpLayoutRawPreparation.program
      (SubexpLayoutRawPreparation.runtimeBound x + 1)
      ((SubexpLayoutRawPreparation.inputState regs x).withPC
        (some SubexpLayoutRawPreparation.program.entry)) ((prepared x).withPC none) := by
    simpa only [prepared, prefixTables, prefixScopes_encoded, variableCount] using
      SubexpLayoutRawPreparation.program_runs regs x hell hwidth
  obtain ⟨p, hpBound, hpTrace⟩ := hp
  obtain ⟨e, heReady, he31, he34, he32, he33, f, hfBound, hfTrace⟩ :=
    SubexpClauseFamilyProgram.program_runsIn (familyInputs x) hv clauses
      (prefixTables x) (prefixScopes x) (projectFamily (prepared x)) (prepared_ready x)
      hsource rfl rfl rfl
  let out := embedState familyRegister familyPort (prepared x) e
  have hf : Eval familyCall f (prepared x) out :=
    eval_call_from_state _ familyRegister familyPort (prepared x)
      familyRegister_injective familyPort_injective hfTrace
  have hpEval : Eval (.call SubexpLayoutRawPreparation.program) p
      (SubexpLayoutRawPreparation.inputState regs x) (prepared x) := .call _ hpTrace
  refine ⟨out, ⟨p + f + 1, ?_, compiled_halt_trace (hpEval.seq hf) 39 32⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold runtimeBound
    omega
  · exact (embedState_stack _ _ _ _ familyPort_injective 32).trans he32
  · exact (embedState_stack _ _ _ _ familyPort_injective 33).trans he33
  · exact (embedState_stack _ _ _ _ familyPort_injective 31).trans he31
  · exact (embedState_stack _ _ _ _ familyPort_injective 34).trans he34
  · simpa only [projectFamily, out,
      projectState_embed _ _ _ _ familyRegister_injective familyPort_injective] using heReady
  · intro i hi
    exact embedState_stack_frame familyRegister familyPort (prepared x) e i (by
      rintro ⟨j, hj⟩
      have hval := congrArg Fin.val hj
      change j.val = i.val at hval
      omega)

end SubexponentialSAT.SubexpLayoutConstruction

end OAI.Algorithms
