import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseFactorProgram
import OAI.Algorithms.SubexponentialSAT.SubexpClauseFamilySupport

namespace OAI.Algorithms

/-! Closed paired-record callback: construct one real clause factor and emit
its table and scope into separate framed streams. -/

namespace SubexponentialSAT.SubexpClauseFamilyCallback

open BitProgram StructuredCalls StackRoutines SubexpClauseFamilySupport

abbrev Inputs := SubexpClauseFactorProgram.Inputs

structure Valid (c : Inputs) (D n : ℕ) : Prop where
  modulus_pos : 0 < BinaryArithmetic.toNat c.modulus
  ell_pos : 0 < BinaryArithmetic.toNat c.binaryEll
  ell_value : BinaryArithmetic.toNat c.binaryEll = c.ellShape.length
  width : c.widthShape.length = c.modulus.length
  ell_width : c.ellShape.length ≤ c.widthShape.length
  full : c.fullShape.length = D * c.ellShape.length
  shape : c.nShape.length = n
  covered : n ≤ c.fullShape.length

def withWord (c : Inputs) (word : List Bool) : Inputs := { c with clause := word }

def withClause {n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n))) : Inputs :=
  withWord c (SubexpClauseRowProgram.clauseBytes ls)

theorem validClause {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) : SubexpClauseFactorProgram.Valid (withClause c ls) D ls :=
  ⟨hv.modulus_pos, hv.ell_pos, hv.ell_value, hv.width, hv.ell_width,
    hv.full, hv.shape, hv.covered, rfl⟩

def scope {D n : ℕ} (c : Inputs) (hv : Valid c D n) (ls : List (SAT.Literal (Fin n))) :=
  SubexpClauseFactorProgram.scopeOf (withClause c ls) ls (validClause c hv ls)

def scopeBytes {n : ℕ} (c : Inputs) (ls : List (SAT.Literal (Fin n))) : List Bool :=
  SubexpClauseFactorProgram.scopeBytes (withClause c ls) ls

def table {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) : List Bool :=
  SubexpClauseFactorProgram.table (withClause c ls) (scope c hv ls) ls

theorem scopeBytes_eq {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) :
    scopeBytes c ls = Encoding.encodeList Encoding.encodeNat ((scope c hv ls).map Fin.val) := by
  unfold scope
  rw [SubexpClauseFactorProgram.scopeOf_values]
  rfl

theorem scope_nodup {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) : (scope c hv ls).Nodup :=
  SubexpClauseFactorProgram.scopeOf_nodup _ _ _

theorem scope_length_le {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) : (scope c hv ls).length ≤ ls.length :=
  SubexpClauseFactorProgram.scopeOf_length_le _ _ _

theorem table_length {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) :
    (table c hv ls).length = BinaryArithmetic.toNat c.modulus ^ (scope c hv ls).length :=
  SubexpClauseFactorProgram.table_length _ _ _

theorem scopeBytes_length_le {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) :
    (scopeBytes c ls).length ≤ 1 + (2 * D + 2) * ls.length :=
  SubexpClauseFactorProgram.scopeBytes_length_le _ _ (validClause c hv ls)

def unitCost {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) : ℕ :=
  SubexpClauseFactorProgram.budget (withClause c ls) (scope c hv ls) ls

def bankReg (i : Fin 11) : Fin 14 := i.castAdd 3
def bankStack (i : Fin 31) : Fin 35 := i.castAdd 4

theorem bankReg_injective : Function.Injective bankReg := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 14 => x.val) h)
theorem bankStack_injective : Function.Injective bankStack := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 35 => x.val) h)

@[simp] theorem bankStack_ne_31 (i : Fin 31) : bankStack i ≠ 31 := by
  intro h; have he := congrArg Fin.val h; change i.val = 31 at he; omega
@[simp] theorem bankStack_ne_32 (i : Fin 31) : bankStack i ≠ 32 := by
  intro h; have he := congrArg Fin.val h; change i.val = 32 at he; omega
@[simp] theorem bankStack_ne_33 (i : Fin 31) : bankStack i ≠ 33 := by
  intro h; have he := congrArg Fin.val h; change i.val = 33 at he; omega
@[simp] theorem bankStack_ne_34 (i : Fin 31) : bankStack i ≠ 34 := by
  intro h; have he := congrArg Fin.val h; change i.val = 34 at he; omega

/-- The six common masters are present, and the whole unit work bank is empty. -/
def Ready (c : Inputs) (d : Data) : Prop :=
  ∀ i : Fin 31, d.stacks (bankStack i) =
    SubexpClauseFactorProgram.tapes (withWord c []) [] [] [] [] [] [] i

abbrev coreCall : Cmd 14 35 := .call
  (ProgramLinking.liftProgram SubexpClauseFactorProgram.program bankReg bankStack)

theorem coreCall_eval {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) (d : Data)
    (hlocal : ∀ i : Fin 31, d.stacks (bankStack i) =
      SubexpClauseFactorProgram.tapes (withClause c ls) [] [] [] [] [] [] i) :
    ∃ t ≤ unitCost c hv ls + 1, ∃ e : Data, Eval coreCall t d e ∧
      e.stacks = Function.update (Function.update d.stacks 24 (scopeBytes c ls)) 29 (table c hv ls) := by
  let a := projectState bankReg bankStack d
  let b := SubexpClauseFactorProgram.data SubexpClauseFactorProgram.zeroRegs
    (withClause c ls) [] [] [] (scopeBytes c ls) [] (table c hv ls)
  have ha : a = SubexpClauseFactorProgram.data (d.regs ∘ bankReg)
      (withClause c ls) [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; exact hlocal i
  obtain ⟨t, ht, trace⟩ := SubexpClauseFactorProgram.program_runsIn_raw
    (withClause c ls) ls (validClause c hv ls) (d.regs ∘ bankReg)
  change Trace SubexpClauseFactorProgram.program t
    ((SubexpClauseFactorProgram.data (d.regs ∘ bankReg)
      (withClause c ls) [] [] [] [] [] []).withPC _) (b.withPC none) at trace
  rw [← ha] at trace
  have he := eval_call_from_state SubexpClauseFactorProgram.program
    bankReg bankStack d bankReg_injective bankStack_injective trace
  have hb : b.stacks = Function.update (Function.update a.stacks 24 (scopeBytes c ls))
      29 (table c hv ls) := by
    rw [ha]
    funext i; fin_cases i <;> simp [b, SubexpClauseFactorProgram.data,
      SubexpClauseFactorProgram.tapes]
  refine ⟨t, ht, embedState bankReg bankStack d b, he, ?_⟩
  change Function.extend bankStack b.stacks d.stacks = _
  rw [hb, ProgramLinking.extend_update bankStack_injective,
    ProgramLinking.extend_update bankStack_injective]
  have hext : Function.extend bankStack a.stacks d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project bankReg bankStack d bankReg_injective bankStack_injective)
  rw [hext]
  rfl

abbrev callback : Cmd 14 35 := .seq (transfer 34 25) (.seq coreCall
  (.seq (clear 25) (.seq (transfer 29 34) (.seq (emit .tables)
    (.seq (transfer 24 34) (emit .scopes))))))

def callbackCost {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) : ℕ :=
  unitCost c hv ls + 5 * (SubexpClauseRowProgram.clauseBytes ls).length +
    8 * (table c hv ls).length + 8 * (scopeBytes c ls).length + 39

/-- Both outputs are records from the same concrete unit execution. -/
theorem callback_eval {D n : ℕ} (c : Inputs) (hv : Valid c D n)
    (ls : List (SAT.Literal (Fin n))) (d : Data) (hc : Ready c d)
    (hq : d.stacks 34 = (SubexpClauseRowProgram.clauseBytes ls).reverse) :
    ∃ t ≤ callbackCost c hv ls, ∃ e : Data, Eval callback t d e ∧ Ready c e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 32
        (true :: (Encoding.frame (table c hv ls) ++ d.stacks 32))) 33
        (true :: (Encoding.frame (scopeBytes c ls) ++ d.stacks 33))) 34 [] ∧
      e.regs 11 = false ∧ e.regs 12 = true ∧ e.regs 13 = false := by
  have hd24 : d.stacks 24 = [] := by simpa [Ready, bankStack,
    SubexpClauseFactorProgram.tapes, withWord] using hc 24
  have hd25 : d.stacks 25 = [] := by simpa [Ready, bankStack,
    SubexpClauseFactorProgram.tapes, withWord] using hc 25
  have hd29 : d.stacks 29 = [] := by simpa [Ready, bankStack,
    SubexpClauseFactorProgram.tapes, withWord] using hc 29
  let a := transferred 34 25 d
  have halocal : ∀ i : Fin 31, a.stacks (bankStack i) =
      SubexpClauseFactorProgram.tapes (withClause c ls) [] [] [] [] [] [] i := by
    intro i
    have hi := hc i
    fin_cases i <;> simp_all [a, transferred, transferStacks, bankStack,
      SubexpClauseFactorProgram.tapes, withClause, withWord]
  obtain ⟨t, ht, b, he, hb⟩ := coreCall_eval c hv ls a halocal
  let d₁ := cleared 25 b
  let d₂ := transferred 29 34 d₁
  let d₃ := emitted .tables (table c hv ls) d₂
  let d₄ := transferred 24 34 d₃
  let e := emitted .scopes (scopeBytes c ls) d₄
  have ha25 : a.stacks 25 = SubexpClauseRowProgram.clauseBytes ls := by
    simp [a, transferred, transferStacks, hq, hd25]
  have hb25 : b.stacks 25 = SubexpClauseRowProgram.clauseBytes ls := by simp [hb, ha25]
  have hd₁29 : d₁.stacks 29 = table c hv ls := by simp [d₁, cleared, clearStacks, hb]
  have hd₂34 : d₂.stacks 34 = (table c hv ls).reverse := by
    simp [d₂, d₁, cleared, transferred, clearStacks, transferStacks, hb, a]
  have hd₃24 : d₃.stacks 24 = scopeBytes c ls := by
    simp [d₃, emitted, Stream.port, d₂, d₁, cleared, transferred, clearStacks,
      transferStacks, hb]
  have hd₄34 : d₄.stacks 34 = (scopeBytes c ls).reverse := by
    change (d₃.stacks 24).reverse ++ d₃.stacks 34 = (scopeBytes c ls).reverse
    rw [hd₃24]
    simp [d₃, emitted]
  have heStacks : e.stacks = Function.update (Function.update (Function.update d.stacks 32
        (true :: (Encoding.frame (table c hv ls) ++ d.stacks 32))) 33
        (true :: (Encoding.frame (scopeBytes c ls) ++ d.stacks 33))) 34 [] := by
    funext i; fin_cases i <;>
      simp [e, d₄, d₃, d₂, d₁, emitted, cleared, transferred, clearStacks,
        transferStacks, hb, a, Stream.port, hd24, hd25, hd29, hq]
  have hrun := (transfer_eval 34 25 (by decide) d).seq
    (he.seq ((clear_eval 25 b).seq ((transfer_eval 29 34 (by decide) d₁).seq
      ((emit_eval .tables (table c hv ls) d₂ hd₂34).seq
        ((transfer_eval 24 34 (by decide) d₃).seq
          (emit_eval .scopes (scopeBytes c ls) d₄ hd₄34))))))
  refine ⟨_, ?_, e, hrun, ?_, heStacks, ?_, ?_, ?_⟩
  · simp only [hq, List.length_reverse, hb25, hd₁29, hd₃24]
    unfold callbackCost
    omega
  · intro i
    simpa [heStacks] using hc i
  · simp [e, emitted, flags]
  · simp [e, emitted, flags]
  · simp [e, emitted, flags]

end SubexponentialSAT.SubexpClauseFamilyCallback

end OAI.Algorithms
