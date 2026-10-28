import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchInputCode
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixDimensionBounds

namespace OAI.Algorithms

/-!
# Physical inputs for one local-basis search

The width is built from the unary color and position counts. The Side list
is then selected from the actual universal-type records, and its dimension
and squared dimension are counted from those selected records. All three
operations use the fixed port maps of `LocalBasisBatchProgram`.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls
open BlockSearchPreparation (restrictState lifted_call)
open TypeIndexProgram (unary)

private theorem embedded_stacks_eq {r s : ℕ}
    (ρ : Fin r → Fin 32) (σ : Fin s → Fin 128)
    (hσ : Function.Injective σ) (a : Data) (b : State r s)
    (target : Fin 128 → Word)
    (mapped : ∀ i, target (σ i) = b.stacks i)
    (frame : ∀ j, (¬ ∃ i, σ i = j) → target j = a.stacks j) :
    (embedState ρ σ a b).stacks = target := by
  funext j
  by_cases hj : ∃ i, σ i = j
  · obtain ⟨i, rfl⟩ := hj
    exact (embedState_stack ρ σ a b hσ i).trans (mapped i).symm
  · exact (embedState_stack_frame ρ σ a b j hj).trans (frame j hj).symm

private theorem embedded_single_update {r s : ℕ}
    (ρ : Fin r → Fin 32) (σ : Fin s → Fin 128)
    (hσ : Function.Injective σ) (a : Data) (b : State r s) (i : Fin s) (value : Word)
    (hlocal : b.stacks = Function.update (a.stacks ∘ σ) i value) :
    (embedState ρ σ a b).stacks = Function.update a.stacks (σ i) value := by
  apply embedded_stacks_eq _ _ hσ
  · intro j
    rw [hlocal]
    simp only [Function.update_apply, Function.comp_apply, hσ.eq_iff]
  · intro j hj
    have hji : j ≠ σ i := fun h => hj ⟨i, h.symm⟩
    simp [hji]

private theorem embedded_double_update {r s : ℕ}
    (ρ : Fin r → Fin 32) (σ : Fin s → Fin 128)
    (hσ : Function.Injective σ) (a : Data) (b : State r s)
    (i j : Fin s) (first second : Word)
    (hlocal : b.stacks = Function.update (Function.update (a.stacks ∘ σ) i first) j second) :
    (embedState ρ σ a b).stacks =
      Function.update (Function.update a.stacks (σ i) first) (σ j) second := by
  apply embedded_stacks_eq _ _ hσ
  · intro k
    rw [hlocal]
    simp only [Function.update_apply, Function.comp_apply, hσ.eq_iff]
  · intro k hk
    have hki : k ≠ σ i := fun h => hk ⟨i, h.symm⟩
    have hkj : k ≠ σ j := fun h => hk ⟨j, h.symm⟩
    simp [hki, hkj]

def widthResult (r Q : ℕ) (a : Data) : Data :=
  ⟨Function.update (readRegs a.regs 0 1 none) 2 false,
    Function.update a.stacks 114 (unary (Q * r))⟩

def widthCost (r Q : ℕ) : ℕ := 7 * Q + Q * (7 * r + 7) + 9

/-- Exact execution, including the initial counter copy, flag reset, and
the halt of the called block-copy program. Only stack 114 changes. -/
theorem makeWidth_eval (r Q : ℕ) (a : Data)
    (hr : a.stacks 112 = unary r) (hQ : a.stacks 113 = unary Q)
    (h0 : a.stacks 0 = []) (h114 : a.stacks 114 = [])
    (h124 : a.stacks 124 = []) (h125 : a.stacks 125 = []) :
    Eval makeWidth (widthCost r Q) a (widthResult r Q a) := by
  let b := copyState 113 124 a
  let c : Data := ⟨Function.update b.regs 2 false, b.stacks⟩
  have hcopy := copy_eval 113 124 a (by decide) (by decide) (by decide) h125
  have hset : Eval (.base (.atom (.set 2 false))) 1 b c := .base (.atom _ _)
  have hi : embedState widthRegisters widthPorts c
      (BlockCopyProgram.initialState Q (unary r) []) = c := by
    apply SubexpScanPrimitives.embedState_eq _ _ widthRegisters_injective widthPorts_injective
    · intro j
      fin_cases j <;> simp [c, b, copyState, widthRegisters, readRegs,
        BlockCopyProgram.initialState, BlockCopyProgram.data]
    · intro j
      fin_cases j <;> simp [c, b, copyState, StackRoutines.copyStacks,
        widthPorts, BlockCopyProgram.initialState, BlockCopyProgram.data, hr, hQ, h0, h114, h124]
    · intros; rfl
    · intros; rfl
  have ho : embedState widthRegisters widthPorts c
      (BlockCopyProgram.data false false (unary r)
        (BlockCopyProgram.copies Q (unary r) ++ []) []) = widthResult r Q a := by
    apply SubexpScanPrimitives.embedState_eq _ _ widthRegisters_injective widthPorts_injective
    · intro j
      fin_cases j <;> simp [widthResult, widthRegisters, readRegs, BlockCopyProgram.data]
    · intro j
      fin_cases j <;> simp [widthResult, widthPorts, BlockCopyProgram.data,
        TypeIndexProgram.copies_unary, hr, h0, h124]
    · intros; rfl
    · intro j hj
      have hj114 : j ≠ 114 := fun h => hj ⟨1, by simpa [widthPorts] using h.symm⟩
      have hj124 : j ≠ 124 := fun h => hj ⟨3, by simpa [widthPorts] using h.symm⟩
      simp [widthResult, c, b, copyState, StackRoutines.copyStacks, hj114, hj124]
  have hcall := eval_call_lifted BlockCopyProgram.program widthRegisters widthPorts c
    widthRegisters_injective widthPorts_injective (BlockCopyProgram.program_trace Q (unary r) [])
  rw [hi, ho] at hcall
  have hrun := hcopy.seq (hset.seq hcall)
  have hlen : (a.stacks 113).length = Q := by simp [hQ, unary]
  rw [hlen] at hrun
  simp only [unary, List.length_replicate] at hrun
  have hcost : 7 * Q + 5 + (1 + (Q * (7 * r + 7) + 3)) = widthCost r Q := by
    unfold widthCost
    ring
  rw [hcost] at hrun
  exact hrun

theorem widthResult_frame (r Q : ℕ) (a : Data) (j : Fin 128) (hj : j ≠ 114) :
    (widthResult r Q a).stacks j = a.stacks j := by simp [widthResult, hj]

theorem widthResult_register_frame (r Q : ℕ) (a : Data) (j : Fin 32) (hj : 3 ≤ j.val) :
    (widthResult r Q a).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
  have h2 : j ≠ 2 := by intro h; subst j; norm_num at hj
  simp [widthResult, readRegs, h0, h1, h2]

/-- A concrete projection condition: all local work words are empty and
every metadata word is the actual unary encoding expected by the filter. -/
def SideReady (ctx : TypeFiberProgram.Context) (records : List Word) (a : Data) : Prop :=
  restrictState fiberRegisters fiberPorts a =
    TypeFiberProgram.inputState ctx records (a.regs ∘ fiberRegisters)

theorem side_ready (ctx : TypeFiberProgram.Context) (records : List Word) (a : Data)
    (hsource : a.stacks 107 = ProgramEncoding.encodeRecords records)
    (hr : a.stacks 112 = unary ctx.r) (ht : a.stacks 117 = unary ctx.t)
    (hg : a.stacks 118 = unary ctx.g) (hw : a.stacks 114 = unary ctx.width)
    (hi : a.stacks 9 = unary ctx.i) (hout : a.stacks 53 = [])
    (hwork : ∀ j : Fin 128, j.val < 9 → a.stacks j = []) : SideReady ctx records a := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext j
    fin_cases j <;> simp [restrictState, fiberPorts, TypeFiberProgram.inputState,
      TypeFiberProgram.state, hsource, hr, ht, hg, hw, hi, hout, hwork]

/-- The lifted Side filter preserves every ambient stack except its output
53. In particular the outer-loop counters and accumulated records survive. -/
theorem sideFilter_eval (ctx : TypeFiberProgram.Context) (records : List Word) (a : Data)
    (ready : SideReady ctx records a) :
    ∃ steps b, steps ≤ TypeFiberProgram.budget false ctx records ∧
      Eval sideFilter steps a b ∧
      b.stacks = Function.update a.stacks 53
        (ProgramEncoding.encodeRecords (TypeFiberProgram.resultWords false ctx records)) ∧
      ∀ j : Fin 32, 8 ≤ j.val → b.regs j = a.regs j := by
  change restrictState fiberRegisters fiberPorts a =
    TypeFiberProgram.inputState ctx records (a.regs ∘ fiberRegisters) at ready
  have hin := congrArg (fun d : TypeFiberProgram.Data => d.stacks) ready
  change a.stacks ∘ fiberPorts =
    (TypeFiberProgram.inputState ctx records (a.regs ∘ fiberRegisters)).stacks at hin
  obtain ⟨rf, hrun⟩ := TypeFiberProgram.program_runsIn false ctx records (a.regs ∘ fiberRegisters)
  obtain ⟨steps, hsteps, he⟩ := lifted_call (TypeFiberProgram.program false)
    fiberRegisters fiberPorts fiberRegisters_injective fiberPorts_injective a
    (TypeFiberProgram.outputState false ctx records rf) (TypeFiberProgram.budget false ctx records)
    (by simpa only [ready] using hrun)
  refine ⟨steps, _, hsteps, he, ?_, ?_⟩
  · change (embedState fiberRegisters fiberPorts a
      (TypeFiberProgram.outputState false ctx records rf)).stacks =
        Function.update a.stacks (fiberPorts 10) _
    apply embedded_single_update _ _ fiberPorts_injective
    rw [hin]
    funext j
    by_cases hj : j = 10
    · subst j
      simp [TypeFiberProgram.inputState, TypeFiberProgram.outputState, TypeFiberProgram.state]
    · simp [TypeFiberProgram.inputState, TypeFiberProgram.outputState, TypeFiberProgram.state, hj]
  · intro j hj
    apply embedState_register_frame
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    simp only [fiberRegisters, Fin.val_castAdd] at hv
    omega

def DimensionsReady (records : List Word) (a : Data) : Prop :=
  restrictState dimensionRegisters dimensionPorts a =
    ConstraintMatrixDimensions.input records (a.regs ∘ dimensionRegisters)

theorem dimensions_ready (records : List Word) (a : Data)
    (hsource : a.stacks 53 = ProgramEncoding.encodeRecords records)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (h3 : a.stacks 3 = []) (h123 : a.stacks 123 = []) (h124 : a.stacks 124 = []) :
    DimensionsReady records a := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext j
    fin_cases j <;> simp [restrictState, dimensionPorts, ConstraintMatrixDimensions.input,
      hsource, h0, h1, h2, h3, h123, h124]

/-- Both dimension words are computed from the saved Side records; they
are not additional runtime advice. The Side bytes themselves are retained. -/
theorem dimensions_eval (records : List Word) (a : Data) (ready : DimensionsReady records a) :
    ∃ steps b, steps ≤ ConstraintMatrixDimensions.budget records ∧
      Eval dimensions steps a b ∧
      b.stacks = Function.update (Function.update a.stacks 123 (unary records.length))
        124 (unary (records.length * records.length)) ∧
      ∀ j : Fin 32, 5 ≤ j.val → b.regs j = a.regs j := by
  change restrictState dimensionRegisters dimensionPorts a =
    ConstraintMatrixDimensions.input records (a.regs ∘ dimensionRegisters) at ready
  have hin := congrArg (fun d : ConstraintMatrixDimensions.Data => d.stacks) ready
  change a.stacks ∘ dimensionPorts =
    (ConstraintMatrixDimensions.input records (a.regs ∘ dimensionRegisters)).stacks at hin
  obtain ⟨rf, hrun⟩ := ConstraintMatrixDimensions.program_runsIn records (a.regs ∘ dimensionRegisters)
  obtain ⟨steps, hsteps, he⟩ := lifted_call ConstraintMatrixDimensions.program
    dimensionRegisters dimensionPorts dimensionRegisters_injective dimensionPorts_injective a
    (ConstraintMatrixDimensions.output records rf) (ConstraintMatrixDimensions.budget records)
    (by simpa only [ready] using hrun)
  refine ⟨steps, _, hsteps, he, ?_, ?_⟩
  · change (embedState dimensionRegisters dimensionPorts a
      (ConstraintMatrixDimensions.output records rf)).stacks =
        Function.update (Function.update a.stacks (dimensionPorts 3) _) (dimensionPorts 4) _
    apply embedded_double_update _ _ dimensionPorts_injective
    rw [hin]
    funext j
    by_cases hj4 : j = 4
    · subst j
      simp [ConstraintMatrixDimensions.input, ConstraintMatrixDimensions.output, unary]
    · by_cases hj3 : j = 3
      · subst j
        simp [ConstraintMatrixDimensions.input, ConstraintMatrixDimensions.output, unary]
      · simp [ConstraintMatrixDimensions.input, ConstraintMatrixDimensions.output, unary, hj3, hj4]
  · intro j hj
    apply embedState_register_frame
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    simp only [dimensionRegisters, Fin.val_castAdd] at hv
    omega

theorem dimensions_eval_quadratic (records : List Word) (a : Data)
    (ready : DimensionsReady records a) :
    ∃ steps b, steps ≤ 32 * ((ProgramEncoding.encodeRecords records).length + 1)^2 ∧
      Eval dimensions steps a b ∧
      b.stacks = Function.update (Function.update a.stacks 123 (unary records.length))
        124 (unary (records.length * records.length)) ∧
      ∀ j : Fin 32, 5 ≤ j.val → b.regs j = a.regs j := by
  obtain ⟨steps, b, hb, he, hs, hr⟩ := dimensions_eval records a ready
  exact ⟨steps, b, hb.trans (ConstraintMatrixDimensions.budget_le_length records), he, hs, hr⟩

def sideDimensionsCost (r Q Δ t g : ℕ) : ℕ :=
  TypeFiberProgram.budget false ⟨r, t, g, Q * r, 0⟩ (TypeEnumeration.universalBytes r Q Δ) +
    ConstraintMatrixDimensions.budget (TypeEnumeration.sideBytes r Q Δ t g)

/-- The exact observed Side order feeds the dimension counter directly.
No sorted or extensionally equivalent replacement list is introduced. -/
theorem side_dimensions_eval (r Q Δ t g : ℕ) (a : Data)
    (hsource : a.stacks 107 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ))
    (hr : a.stacks 112 = unary r) (ht : a.stacks 117 = unary t)
    (hg : a.stacks 118 = unary g) (hw : a.stacks 114 = unary (Q * r))
    (hwork : ∀ j : Fin 128, j.val < 10 → a.stacks j = [])
    (h53 : a.stacks 53 = []) (h123 : a.stacks 123 = []) (h124 : a.stacks 124 = []) :
    ∃ steps b, steps ≤ sideDimensionsCost r Q Δ t g ∧
      Eval (.seq sideFilter dimensions) steps a b ∧
      b.stacks = Function.update (Function.update (Function.update a.stacks 53
        (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t g)))
        123 (unary (TypeEnumeration.sideBytes r Q Δ t g).length))
        124 (unary ((TypeEnumeration.sideBytes r Q Δ t g).length *
          (TypeEnumeration.sideBytes r Q Δ t g).length)) ∧
      ∀ j : Fin 32, 8 ≤ j.val → b.regs j = a.regs j := by
  have hready := side_ready ⟨r, t, g, Q * r, 0⟩ (TypeEnumeration.universalBytes r Q Δ) a
    hsource hr ht hg hw (by simpa [unary] using hwork 9 (by decide)) h53
    (fun j hj => hwork j (by omega))
  obtain ⟨ns, b, hns, hes, hbs, hrs⟩ := sideFilter_eval _ _ a hready
  rw [TypeFiberProgram.side_result] at hbs
  have hdready : DimensionsReady (TypeEnumeration.sideBytes r Q Δ t g) b := by
    apply dimensions_ready
    · rw [hbs]; simp
    · rw [hbs]; simp [hwork 0 (by decide)]
    · rw [hbs]; simp [hwork 1 (by decide)]
    · rw [hbs]; simp [hwork 2 (by decide)]
    · rw [hbs]; simp [hwork 3 (by decide)]
    · rw [hbs]; simp [h123]
    · rw [hbs]; simp [h124]
  obtain ⟨nd, c, hnd, hed, hcs, hrc⟩ := dimensions_eval _ b hdready
  refine ⟨ns + nd, c, Nat.add_le_add hns hnd, hes.seq hed, ?_, ?_⟩
  · simpa only [hbs] using hcs
  · intro j hj
    exact (hrc j (by omega)).trans (hrs j hj)

def prepareInputCommand : Code := .seq makeWidth (.seq sideFilter dimensions)
def prepareInputProgram := compiled prepareInputCommand 107 124

/-- Closed composition of width construction, Side selection, and dimension
counting. The existing caller data is retained outside the four result words. -/
theorem prepare_inputs_eval (r Q Δ t g : ℕ) (a : Data)
    (hsource : a.stacks 107 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ))
    (hr : a.stacks 112 = unary r) (hQ : a.stacks 113 = unary Q)
    (ht : a.stacks 117 = unary t) (hg : a.stacks 118 = unary g)
    (hwork : ∀ j : Fin 128, j.val < 10 → a.stacks j = [])
    (h53 : a.stacks 53 = []) (h114 : a.stacks 114 = [])
    (h123 : a.stacks 123 = []) (h124 : a.stacks 124 = []) (h125 : a.stacks 125 = []) :
    ∃ steps b, steps ≤ widthCost r Q + sideDimensionsCost r Q Δ t g ∧
      Eval prepareInputCommand steps a b ∧
      b.stacks = Function.update (Function.update (Function.update
        (Function.update a.stacks 114 (unary (Q * r))) 53
        (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t g)))
        123 (unary (TypeEnumeration.sideBytes r Q Δ t g).length))
        124 (unary ((TypeEnumeration.sideBytes r Q Δ t g).length *
          (TypeEnumeration.sideBytes r Q Δ t g).length)) ∧
      ∀ j : Fin 32, 8 ≤ j.val → b.regs j = a.regs j := by
  have hw := makeWidth_eval r Q a hr hQ (hwork 0 (by decide)) h114 h124 h125
  obtain ⟨steps, b, hb, he, hs, hf⟩ := side_dimensions_eval r Q Δ t g (widthResult r Q a)
    (by simpa [widthResult] using hsource) (by simpa [widthResult] using hr)
    (by simpa [widthResult] using ht) (by simpa [widthResult] using hg)
    (by simp [widthResult])
    (by
      intro j hj
      have hj114 : j ≠ 114 := by
        intro h
        subst j
        exact (by decide : ¬ (114 : Fin 128).val < 10) hj
      simpa [widthResult, hj114] using hwork j hj)
    (by simpa [widthResult] using h53) (by simpa [widthResult] using h123)
    (by simpa [widthResult] using h124)
  refine ⟨widthCost r Q + steps, b, Nat.add_le_add_left hb _, hw.seq he, hs, ?_⟩
  intro j hj
  exact (hf j hj).trans (widthResult_register_frame r Q a j (by omega))

theorem prepare_inputs_runsIn (r Q Δ t g : ℕ) (a : Data)
    (hsource : a.stacks 107 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ))
    (hr : a.stacks 112 = unary r) (hQ : a.stacks 113 = unary Q)
    (ht : a.stacks 117 = unary t) (hg : a.stacks 118 = unary g)
    (hwork : ∀ j : Fin 128, j.val < 10 → a.stacks j = [])
    (h53 : a.stacks 53 = []) (h114 : a.stacks 114 = [])
    (h123 : a.stacks 123 = []) (h124 : a.stacks 124 = []) (h125 : a.stacks 125 = []) :
    ∃ b : Data, RunsIn prepareInputProgram (widthCost r Q + sideDimensionsCost r Q Δ t g + 1)
      (a.withPC (some prepareInputProgram.entry)) (b.withPC none) ∧
      b.stacks = Function.update (Function.update (Function.update
        (Function.update a.stacks 114 (unary (Q * r))) 53
        (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t g)))
        123 (unary (TypeEnumeration.sideBytes r Q Δ t g).length))
        124 (unary ((TypeEnumeration.sideBytes r Q Δ t g).length *
          (TypeEnumeration.sideBytes r Q Δ t g).length)) ∧
      ∀ j : Fin 32, 8 ≤ j.val → b.regs j = a.regs j := by
  obtain ⟨steps, b, hb, he, hs, hf⟩ := prepare_inputs_eval r Q Δ t g a
    hsource hr hQ ht hg hwork h53 h114 h123 h124 h125
  exact ⟨b, ⟨steps + 1, Nat.add_le_add_right hb 1, compiled_halt_trace he 107 124⟩, hs, hf⟩

/-- Semantic cardinality of the physically counted Side list. The
equivalence only names its existing order and is not run by the machine. -/
theorem side_dimension_eq_card {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) :
    (TypeEnumeration.sideBytes r Q Δ t.val g.val).length =
      Fintype.card (MulticolorTypes.Side (Δ := Δ) t g) := by
  rw [← TypeEnumeration.sideList_bytes hr hQ t g, List.length_map]
  simpa only [Fintype.card_fin] using Fintype.card_congr (TypeEnumeration.sideEquiv hr hQ t g)

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
