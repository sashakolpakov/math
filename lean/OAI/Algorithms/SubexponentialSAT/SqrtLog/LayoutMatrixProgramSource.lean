import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramPrimitives
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramParser
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Pair := List Bool × List Bool

def pairLength (p : Pair) : ℕ := p.1.length+p.2.length

def bankPort (i : Fin 256) : Fin 288 := ⟨i.val+25,by omega⟩
theorem bankPort_injective : Function.Injective bankPort := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [bankPort] at this
  omega

@[simp] theorem bankPort_eq (i : Fin 256) (j : Fin 256) :
    bankPort i=bankPort j ↔ i=j := bankPort_injective.eq_iff

private theorem bankPort_ne_low (i : Fin 256) (j : Fin 288) (h : j.val < 25) :
    bankPort i ≠ j := by
  intro he
  have := congrArg Fin.val he
  simp [bankPort] at this
  omega
private theorem bankPort_ne_high (i : Fin 256) (j : Fin 288) (h : 280 < j.val) :
    bankPort i ≠ j := by
  intro he
  have := congrArg Fin.val he
  simp [bankPort] at this
  have := i.isLt
  omega

structure Store where
  rowIndex : List Bool := []
  columnIndex : List Bool := []
  positive : List Bool := []
  negative : List Bool := []
  remaining : List Bool := []
  reversedIDs : List Bool := []
  todo : List Bool := []
  row : List Bool := []
  matrix : List Bool := []

def state (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) : Data 288 :=
  ⟨regs,fun i => if i=277 then q.rowIndex else if i=278 then q.columnIndex else
    if i=279 then q.positive else if i=280 then q.negative else if i=281 then q.remaining else
    if i=282 then q.reversedIDs else if i=283 then q.todo else if i=284 then q.row else
    if i=24 then q.matrix else base i⟩

def entryState (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (row col P N : List Bool) : Data 256 :=
  ⟨regs,fun i => if i=252 then row else if i=253 then col else
    if i=254 then P else if i=255 then N else base (bankPort i)⟩

/-- This is a native command contract, not an entry-value oracle. Instantiation
requires an actual Eval of the fixed finite instruction program. Cache and
workspace contents are restored exactly; only the four entry ports vary. -/
def EntryContract (entry : Code 256) (base : Fin 288 → List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ) : Prop :=
  ∀ (regs : Fin 16 → Bool) (j v : ℕ), Valid j v →
    ∃ t ≤ T, ∃ rf result,
      Eval entry t (entryState base regs (List.replicate j true) (List.replicate v true) [] [])
        (entryState base rf (List.replicate j true) (List.replicate v true) result.1 result.2) ∧
      Rel j v result ∧ pairLength result ≤ B

def entryCall (entry : Code 256) : Code 288 :=
  .call (ProgramLinking.liftProgram (compiled entry 252 254) id bankPort)

private theorem project_entry (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    projectState id bankPort (state base regs q) =
      entryState base regs q.rowIndex q.columnIndex q.positive q.negative := by
  apply congrArg (StructuredProgram.State.mk regs)
  funext i
  have h24 := bankPort_ne_low i 24 (by decide)
  have h281 := bankPort_ne_high i 281 (by decide)
  have h282 := bankPort_ne_high i 282 (by decide)
  have h283 := bankPort_ne_high i 283 (by decide)
  have h284 := bankPort_ne_high i 284 (by decide)
  change (if bankPort i=bankPort 252 then _ else if bankPort i=bankPort 253 then _ else
    if bankPort i=bankPort 254 then _ else if bankPort i=bankPort 255 then _ else _) = _
  simp [h24,h281,h282,h283,h284]

private theorem embed_entry (base : Fin 288 → List Bool) (regs rf : Fin 16 → Bool)
    (q : Store) (P N : List Bool) :
    embedState id bankPort (state base regs q)
      (entryState base rf q.rowIndex q.columnIndex P N) =
      state base rf {q with positive:=P,negative:=N} := by
  apply embedState_eq_of_ports id bankPort _ _ _ Function.injective_id bankPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    have h := congrArg (fun d : Data 256 => d.stacks i)
      (project_entry base rf {q with positive:=P,negative:=N})
    exact h
  · intro i hi
    have h279 : i ≠ 279 := fun h => hi ⟨254,by simpa [bankPort] using h.symm⟩
    have h280 : i ≠ 280 := fun h => hi ⟨255,by simpa [bankPort] using h.symm⟩
    simp [state,h279,h280]

theorem entryCall_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B)
    (regs : Fin 16 → Bool) (q : Store) (j v : ℕ) (hv : Valid j v)
    (hj : q.rowIndex=List.replicate j true) (hcol : q.columnIndex=List.replicate v true)
    (hp : q.positive=[]) (hn : q.negative=[]) :
    ∃ t ≤ T+1, ∃ rf result,
      Eval (entryCall entry) t (state base regs q)
        (state base rf {q with positive:=result.1,negative:=result.2}) ∧
      Rel j v result ∧ pairLength result ≤ B := by
  obtain ⟨t,ht,rf,result,he,hr,hb⟩ := hc regs j v hv
  have hs : projectState id bankPort (state base regs q)=
      entryState base regs (List.replicate j true) (List.replicate v true) [] [] := by
    rw [project_entry,hj,hcol,hp,hn]
  rw [←hs] at he
  have hh := eval_call_lifted (compiled entry 252 254) id bankPort (state base regs q)
    Function.injective_id bankPort_injective (compiled_halt_trace he 252 254)
  rw [embedState_project id bankPort _ Function.injective_id bankPort_injective] at hh
  rw [←hj,←hcol,embed_entry] at hh
  exact ⟨t+1,by omega,rf,result,hh,hr,hb⟩

theorem update_rowIndex (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 277 word =
      (state base regs {q with rowIndex:=word}).stacks := by
  funext i
  by_cases h : i=277
  · subst i; simp [state]
  · simp [state,h]

theorem update_columnIndex (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 278 word =
      (state base regs {q with columnIndex:=word}).stacks := by
  funext i
  by_cases h : i=278
  · subst i; simp [state]
  · simp [state,h]

theorem update_positive (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 279 word =
      (state base regs {q with positive:=word}).stacks := by
  funext i
  by_cases h : i=279
  · subst i; simp [state]
  · simp [state,h]

theorem update_negative (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 280 word =
      (state base regs {q with negative:=word}).stacks := by
  funext i
  by_cases h : i=280
  · subst i; simp [state]
  · simp [state,h]

theorem update_remaining (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 281 word =
      (state base regs {q with remaining:=word}).stacks := by
  funext i
  by_cases h : i=281
  · subst i; simp [state]
  · simp [state,h]

theorem update_reversedIDs (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 282 word =
      (state base regs {q with reversedIDs:=word}).stacks := by
  funext i
  by_cases h : i=282
  · subst i; simp [state]
  · simp [state,h]

theorem update_todo (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 283 word =
      (state base regs {q with todo:=word}).stacks := by
  funext i
  by_cases h : i=283
  · subst i; simp [state]
  · simp [state,h]

theorem update_row (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 284 word =
      (state base regs {q with row:=word}).stacks := by
  funext i
  by_cases h : i=284
  · subst i; simp [state]
  · simp [state,h]

theorem update_matrix (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 24 word =
      (state base regs {q with matrix:=word}).stacks := by
  funext i
  by_cases h : i=24
  · subst i; simp [state]
  · simp [state,h]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
