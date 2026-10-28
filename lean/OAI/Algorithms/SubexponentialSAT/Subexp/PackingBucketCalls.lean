import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingUnaryMin
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram

namespace OAI.Algorithms

/-! Physical subroutine calls for the all-type packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketCalls

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 15

def state (regs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool) : Data :=
  ⟨regs, ![rows, [], query, [], [], bucket, saved, keys, [], scan,
    minimum, table, [], count, result]⟩

def bucketRegs (i : Fin 5) : Fin 8 := Fin.castAdd 3 i
def bucketPorts (i : Fin 6) : Fin 15 := Fin.castAdd 9 i
def countPorts : Fin 3 → Fin 15 := ![9, 1, 13]
def minimumPorts : Fin 3 → Fin 15 := ![10, 13, 14]

theorem bucketRegs_injective : Function.Injective bucketRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 8 => z.val) h)

theorem bucketPorts_injective : Function.Injective bucketPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 15 => z.val) h)

theorem countPorts_injective : Function.Injective countPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [countPorts]

theorem minimumPorts_injective : Function.Injective minimumPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [minimumPorts]

def scanProgram := compiled BucketProgram.scan 0 5

abbrev bucketCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram scanProgram bucketRegs bucketPorts)

abbrev countCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram PackingFrameCount.program id countPorts)

abbrev minimumCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram PackingUnaryMin.program id minimumPorts)

def merged (base : Fin 8 → Bool) (localRegs : Fin 5 → Bool) : Fin 8 → Bool :=
  ![localRegs 0, localRegs 1, localRegs 2, localRegs 3, localRegs 4, base 5, base 6, base 7]

private theorem embed_bucket (regs : Fin 8 → Bool) (localRegs : Fin 5 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool)
    (rows' query' bucket' : List Bool) :
    embedState bucketRegs bucketPorts
      (state regs rows query bucket saved keys scan minimum table count result)
      (SubexpRecordScan.recordState localRegs rows' [] query' [] [] bucket') =
    state (merged regs localRegs) rows' query' bucket' saved keys scan minimum table count result := by
  apply SelectorMapProgram.embed_eq _ _ bucketRegs_injective bucketPorts_injective
  · intro i
    fin_cases i <;> simp [bucketRegs, merged, state ]
  · intro i
    fin_cases i <;>
      simp [bucketPorts, state, SubexpRecordScan.storage]
  · intro j hj
    fin_cases j <;> simp_all [bucketRegs, merged, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
        exact False.elim (hj 4 rfl)
  · intro j hj
    fin_cases j <;> simp_all [bucketPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
        exact False.elim (hj 4 rfl) | exact False.elim (hj 5 rfl)

theorem merged_restrict (regs : Fin 8 → Bool) :
    merged regs (fun i => regs (bucketRegs i)) = regs := by
  funext i
  fin_cases i <;> rfl

theorem frames_eq_words (xs : List (List Bool)) : BucketProgram.frames xs = words xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [BucketProgram.frames, words, ih]

/-- One real scan consumes a copied reversed label table, retaining the query
and producing the bucket in original vertex order. -/
theorem bucketCall_eval (records : List BucketProgram.Record) (query : List Bool)
    (regs : Fin 8 → Bool) (saved keys scan minimum table count result : List Bool) :
    ∃ n ≤ 2 + BucketProgram.loopBudget records.reverse query, ∃ regs',
      Eval bucketCall n
        (state regs (BucketProgram.encodeRecords records.reverse) query.reverse []
          saved keys scan minimum table count result)
        (state regs' [] query.reverse (words (BucketProgram.selected records query))
          saved keys scan minimum table count result) := by
  let localRegs : Fin 5 → Bool := fun i => regs (bucketRegs i)
  obtain ⟨n, hn, rf, ht⟩ := BucketProgram.scan_eval localRegs records.reverse query []
  have hh := compiled_halt_trace ht 0 5
  have he := eval_call_lifted scanProgram bucketRegs bucketPorts
    (state regs (BucketProgram.encodeRecords records.reverse) query.reverse []
      saved keys scan minimum table count result)
    bucketRegs_injective bucketPorts_injective hh
  rw [embed_bucket, embed_bucket, merged_restrict] at he
  refine ⟨n + 1, by omega, merged regs rf, ?_⟩
  simpa only [BucketProgram.scanOutput_reverse, frames_eq_words, List.append_nil] using he

private theorem embed_count (regs localRegs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool)
    (scan' count' : List Bool) :
    embedState id countPorts
      (state regs rows query bucket saved keys scan minimum table count result)
      (PackingFrameCount.state localRegs scan' [] count') =
    state localRegs rows query bucket saved keys scan' minimum table count' result := by
  apply SelectorMapProgram.embed_eq _ _ Function.injective_id countPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> simp [countPorts, state ]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    fin_cases j <;> simp_all [countPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl)

theorem countCall_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (rows query bucket saved keys minimum table result : List Bool) :
    ∃ n ≤ 11 * (words xs).length + 3, ∃ regs',
      Eval countCall n
        (state regs rows query bucket saved keys (words xs) minimum table [] result)
        (state regs' rows query bucket saved keys [] minimum table
          (List.replicate xs.length true) result) := by
  obtain ⟨n, hn, rf, ht⟩ := PackingFrameCount.program_trace xs regs []
  have he := eval_call_lifted PackingFrameCount.program id countPorts
    (state regs rows query bucket saved keys (words xs) minimum table [] result)
    Function.injective_id countPorts_injective ht
  rw [embed_count, embed_count] at he
  exact ⟨n, hn, rf, by simpa only [List.append_nil] using he⟩

private theorem embed_minimum (regs localRegs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool)
    (minimum' count' result' : List Bool) :
    embedState id minimumPorts
      (state regs rows query bucket saved keys scan minimum table count result)
      (PackingUnaryMin.state localRegs minimum' count' result') =
    state localRegs rows query bucket saved keys scan minimum' table count' result' := by
  apply SelectorMapProgram.embed_eq _ _ Function.injective_id minimumPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> simp [minimumPorts, state, PackingUnaryMin.state]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    fin_cases j <;> simp_all [minimumPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl)

theorem minimumCall_eval (m n : ℕ) (regs : Fin 8 → Bool)
    (rows query bucket saved keys scan table : List Bool) :
    ∃ steps ≤ 9 * (m + n) + 12, ∃ regs',
      Eval minimumCall steps
        (state regs rows query bucket saved keys scan (List.replicate m true)
          table (List.replicate n true) [])
        (state regs' rows query bucket saved keys scan [] table []
          (List.replicate (min m n) true)) := by
  obtain ⟨steps, ht, rf, hrun⟩ := PackingUnaryMin.program_trace
    (List.replicate m true) (List.replicate n true) [] regs
  have he := eval_call_lifted PackingUnaryMin.program id minimumPorts
    (state regs rows query bucket saved keys scan (List.replicate m true)
      table (List.replicate n true) [])
    Function.injective_id minimumPorts_injective hrun
  rw [embed_minimum, embed_minimum] at he
  exact ⟨steps, by simpa only [List.length_replicate] using ht, rf,
    by simpa only [List.length_replicate, List.append_nil] using he⟩

end SubexponentialSAT.Subexp.PackingBucketCalls

end OAI.Algorithms
