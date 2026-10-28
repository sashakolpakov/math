import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramSemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def baseStacks (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Fin 64 → List Bool :=
  fun i => if i=30 then unary n else if i=31 then low else if i=32 then unary z
    else if i=33 then rows.flatten else if i=38 then unary W else []

def input (regs : Fin 16 → Bool) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  ⟨regs,baseStacks n rows low W z⟩

def result (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  ⟨fun _ => false,
    Function.update (Function.update (baseStacks n rows low W z) 0
      (ProgramEncoding.encodeRecords ((chosenIds (predicate rows low z) n).map unary)))
      1 (zeros (count (predicate rows low z) n))⟩

abbrev setup := HeadIdentifierProgram.setup
abbrev command := HeadIdentifierProgram.command
abbrev program := HeadIdentifierProgram.program

def preparedStacks (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Fin 64 → List Bool :=
  Function.update (Function.update (baseStacks n rows low W z) 39 (unary n)) 0 [false]

theorem setup_eval (regs : Fin 16 → Bool) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    ∃ e, Eval setup (7*n+7) (input regs n rows low W z) e ∧
      e.stacks=preparedStacks n rows low W z := by
  let d := input regs n rows low W z
  let a := afterCopy d 30 39 0 1
  let e := Subexp.TupleProgram.pushedState 0 0 false a
  have h1 : Eval (copy 30 39) (7*n+5) d a := by
    have he := copy_eval d 30 39 42 0 1 (by decide) (by decide) (by decide) (by decide) rfl
    simpa [Subexp.SupportSelectionProgram.copy, a, d, input, baseStacks] using he
  have h2 := Subexp.TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) false a
  refine ⟨e,?_,?_⟩
  · simpa only [setup, HeadIdentifierProgram.setup, Nat.add_assoc,
      Nat.reduceAdd] using h1.seq h2
  · funext i
    by_cases h39 : i=39
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    by_cases h0 : i=0
    · subst i; simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks]
    · simp [e,a,d,afterCopy,StackRoutines.copyStacks,
        input,preparedStacks,baseStacks,h0,h39]

def budget (n totalRows W L z : ℕ) := n*(visitBound totalRows W L z+2)+7*n+26

theorem program_runsIn (regs : Fin 16 → Bool) (n : ℕ) (rows : List (List Bool)) (low : List Bool)
    (W z : ℕ) (hrows : ∀ row ∈ rows,row.length=W) (hn : n ≤ rows.length) :
    RunsIn program (budget n rows.length W low.length z)
      ((input regs n rows low W z).withPC (some program.entry))
      ((result n rows low W z).withPC none) := by
  obtain ⟨d,hs,hsd⟩ := setup_eval regs n rows low W z
  have hdClean : Clean d := by
    intro i hi
    fin_cases i <;> first
    | exact absurd hi (by decide)
    | simp [hsd,preparedStacks,baseStacks]
  obtain ⟨costs,nl,e,hv,hnl,hse⟩ := loop_visits rows low W z hrows n d hn
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks,baseStacks])
    (by simp [hsd,preparedStacks]) hdClean
  have hz := RegisterResetProgram.all_eval e
  have hout : RegisterResetProgram.zeroed e=result n rows low W z := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [hse,hsd,preparedStacks,baseStacks,result,
        Subexp.SupportSelectionProgram.prefix_encode,ProgramEncoding.encodeRecords,
        Subexp.SupportSelectionProgram.indexWords,chosenIds]
  rw [hout] at hz
  have he := hs.seq (hv.eval.seq hz)
  refine ⟨7*n+7+(nl+16)+1,?_,compiled_halt_trace he 30 0⟩
  unfold budget
  omega

theorem budget_polynomial (n totalRows W L z : ℕ) (hn : n ≤ totalRows) :
    budget n totalRows W L z ≤ 300*(totalRows+W+L+z+1)^3 := by
  calc
    _ ≤ HeadIdentifierProgram.budget totalRows W L z := by
      unfold budget HeadIdentifierProgram.budget
      gcongr
    _ ≤ _ := HeadIdentifierProgram.budget_polynomial totalRows W L z

theorem program_primitive (regs : Fin 16 → Bool) (n : ℕ) (rows : List (List Bool)) (low : List Bool)
    (W z : ℕ) (hrows : ∀ row ∈ rows,row.length=W) (hn : n ≤ rows.length) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program*budget n rows.length W low.length z)
      (primitiveCfg program ((input regs n rows low W z).withPC (some program.entry)))
      (primitiveCfg program ((result n rows low W z).withPC none)) :=
  primitive_execution program (program_runsIn regs n rows low W z hrows hn)

theorem scatter_abi (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (result n rows low W z).stacks 0 =
      HeadScatterProgram.indices (chosenIds (predicate rows low z) n) := rfl

theorem count_abi (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) :
    (result n rows low W z).stacks 1 =
      List.replicate (count (predicate rows low z) n) false := rfl

theorem result_frame (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (i : Fin 64) (h0 : i≠0) (h1 : i≠1) :
    (result n rows low W z).stacks i=baseStacks n rows low W z i := by
  simp [result,h0,h1]

/-- Appended factor rows stay in the saved table and are never visited by
this head-prefix scan. Their presence does not change any selected ID. -/
theorem chosenIds_append (heads tail : List (List Bool)) (low : List Bool) (z : ℕ) :
    chosenIds (predicate (heads++tail) low z) heads.length =
      chosenIds (predicate heads low z) heads.length := by
  apply List.filter_congr
  intro j hj
  unfold predicate
  rw [List.getD_append heads tail [] j (List.mem_range.mp hj)]

theorem chosenIds_head_suffix {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (tail : List (List Bool)) (low : List Bool) (z : ℕ) :
    chosenIds (predicate (headRows head++tail) low z) n =
      chosenIds (predicate (headRows head) low z) n := by
  have hl : (headRows head).length=n := by simp [headRows]
  simpa only [hl] using chosenIds_append (headRows head) tail low z

theorem count_head_suffix {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (tail : List (List Bool)) (low : List Bool) (z : ℕ) :
    count (predicate (headRows head++tail) low z) n =
      count (predicate (headRows head) low z) n :=
  congrArg List.length (chosenIds_head_suffix head tail low z)

theorem typed_chosen_mem {n r Q : ℕ} (head : Fin n → MulticolorTypes.Word r Q)
    (tail : List (List Bool)) (low : Fin n → Bool) (t : Fin Q) (g : Fin r) (v : Fin n) :
    v.val ∈ chosenIds (predicate (headRows head++tail) (lowBits low) (t.val*r+g.val)) n ↔
      low v=true ∧ head v t=g := by
  rw [chosenIds_head_suffix]
  exact HeadIdentifierProgram.typed_chosen_mem head low t g v

theorem typed_program_runsIn {n r Q : ℕ} (regs : Fin 16 → Bool)
    (head : Fin n → MulticolorTypes.Word r Q) (tail : List (List Bool))
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r)
    (htail : ∀ row ∈ tail,row.length=Q*r) :
    RunsIn program (budget n (n+tail.length) (Q*r) n (t.val*r+g.val))
      ((input regs n (headRows head++tail) (lowBits low) (Q*r) (t.val*r+g.val)).withPC
        (some program.entry))
      ((result n (headRows head++tail) (lowBits low) (Q*r) (t.val*r+g.val)).withPC none) := by
  have hw : ∀ row ∈ headRows head++tail,row.length=Q*r := by
    intro row hr
    rcases List.mem_append.mp hr with hr | hr
    · exact headRows_width head row hr
    · exact htail row hr
  simpa only [List.length_append,headRows,List.length_ofFn,lowBits] using
    program_runsIn regs n (headRows head++tail) (lowBits low) (Q*r) (t.val*r+g.val) hw
      (by simp [headRows])

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable

end OAI.Algorithms
