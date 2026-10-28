import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

/-! The actual root selector call and its typed Appendix A certificates.
The success and terminal conclusions, return instruction, and every-prefix
storage estimate all describe the same concrete execution. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement

open BitProgram StructuredCalls SparseDFSProgram SparsePriorityProgram

variable {n : ℕ}

def literalWord (l : SAT.Literal (Fin n)) : List Bool :=
  Encoding.encodeNat (Encoding.literalCode l)

theorem literalWord_injective : Function.Injective (literalWord (n := n)) :=
  Encoding.encodeNat_injective.comp Encoding.literalCode_injective

theorem clause_words (H : List (SAT.Literal (Fin n))) :
    Filter.clauseCode (H.map literalWord) =
      ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode) := by
  induction H with
  | nil => rfl
  | cons l H ih =>
    change true :: (Encoding.frame (literalWord l) ++ Filter.clauseCode (H.map literalWord)) =
      true :: (Encoding.frame (literalWord l) ++
        ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode))
    rw [ih]

theorem body_words (F : RawCNF n) :
    Filter.formulaCode (F.map (List.map literalWord)) = SparseCountProgram.encodeBody F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    change true :: (Encoding.frame (Filter.clauseCode (C.map literalWord)) ++
        Filter.formulaCode (F.map (List.map literalWord))) =
      true :: (Encoding.frame (ExecCoreChildProgram.clauseCode (C.map Encoding.literalCode)) ++
        SparseCountProgram.encodeBody F)
    rw [clause_words, ih]

def inputVolume (F : RawCNF n) (base : List Bool) : ℕ :=
  (SparseCountProgram.encodeBody F).length + base.length + 1

theorem inputVolume_eq (F : RawCNF n) (base : List Bool) :
    Selector.inputVolume (F.map (List.map literalWord)) base = inputVolume F base := by
  rw [Selector.inputVolume, body_words, inputVolume]

theorem projection_boundary (F : RawCNF n) (base : List Bool) (d : Data)
    (hF : d.stacks 265 = SparseCountProgram.encodeBody F) (hM : d.stacks 259 = base)
    (hclean : ∀ i : Fin 1220, i.val < 24 → d.stacks i = []) :
    Selector.Boundary (F.map (List.map literalWord)) base
      (projectState (registers 24 (by decide)) selectorStack d) := by
  constructor
  · change d.stacks 265 = _
    rw [hF, body_words]
  · exact hM
  · intro i hi13 hi19
    change d.stacks (selectorStack i) = []
    apply hclean
    have hports : ∀ j : Fin 24, j ≠ 13 → j ≠ 19 → (selectorStack j).val < 24 := by decide
    exact hports i hi13 hi19

/-- The actual root call preserves every physical stack except its two output
ports. A failed call restores those ports too and proves the sharp leaf cap. -/
theorem selectCurrent_execution {k : ℕ} (F : RawCNF n) (base : List Bool)
    (d : Data) (frameBound : ℕ) (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat base)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup)
    (hF : d.stacks 265 = SparseCountProgram.encodeBody F) (hbase : d.stacks 259 = base)
    (hclean : ∀ i : Fin 1220, i.val < 24 → d.stacks i = [])
    (hbound : ∀ i, (d.stacks i).length ≤ frameBound) :
    ∃ t ≤ Selector.selectorCoefficient k * inputVolume F base ^ 4 + 1, ∃ e : Data,
      Eval (selectCurrent k) t d e ∧
      (∀ i : Fin 1220, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧ e.stacks 9 = [] ∧ e.stacks 12 = [] ∧
        SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) = none ∧
        (∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
        ∀ v, SAT.occurrences v (ExecCNF.formulaSet F) ≤
          4 * BinaryArithmetic.toNat base ^ (k - 1)) ∧
      (e.regs 23 = true → ∃ c H,
        RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        SparsePriority.Priority (ExecCNF.formulaSet F) (BinaryArithmetic.toNat base) c
          (ExecCNF.clauseSet H) ∧
        e.stacks 9 = ExecCoreChildProgram.clauseCode (H.map Encoding.literalCode) ∧
        e.stacks 12 = SparseCountProgram.encodeBody (selectedRaw F c H)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (compiled (selectCurrent k) 256 256) prefixSteps
          (d.withPC (some (compiled (selectCurrent k) 256 256).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max ((Selector.selectorCoefficient k + 24) * inputVolume F base ^ 4) frameBound) := by
  let a := projectState (registers 24 (by decide)) selectorStack d
  have ha : Selector.Boundary (F.map (List.map literalWord)) base a :=
    projection_boundary F base d hF hbase hclean
  obtain ⟨t, ht, localFinal, he, hframe, hmiss, hhit, hspace⟩ :=
    SparseDFSResource.selectCurrent_execution_space literalWord literalWord_injective k F base
      a d frameBound ha hwidth hbound
  have hstart : embedState (registers 24 (by decide)) selectorStack d a = d :=
    embedState_project _ _ d (registers 24 (by decide)).injective selectorStack.injective
  rw [hstart] at he hspace
  rw [inputVolume_eq] at ht hspace
  let e := embedState (registers 24 (by decide)) selectorStack d localFinal
  have hflag : e.regs 23 = localFinal.regs 23 :=
    embedState_register (registers 24 (by decide)) selectorStack d localFinal
      (registers 24 (by decide)).injective 23
  have hstack (i : Fin 24) : e.stacks (selectorStack i) = localFinal.stacks i :=
    embedState_stack (registers 24 (by decide)) selectorStack d localFinal selectorStack.injective i
  have hstackFrame (i : Fin 1220) (hi : ¬ ∃ j, selectorStack j = i) : e.stacks i = d.stacks i :=
    embedState_stack_frame (registers 24 (by decide)) selectorStack d localFinal i hi
  have hphysical (i : Fin 1220) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : e.stacks i = d.stacks i := by
    by_cases hi : ∃ j, selectorStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hstack]
      apply hframe j
      · intro h; subst j; exact hi9 rfl
      · intro h; subst j; exact hi12 rfl
    · exact hstackFrame i hi
  refine ⟨t + 1, by omega, e, he, hphysical, ?_, ?_, hspace⟩
  · intro hfalse
    obtain ⟨hs, hfails⟩ := hmiss (hflag.symm.trans hfalse)
    have hes : e.stacks = d.stacks := by
      funext i
      by_cases hi : ∃ j, selectorStack j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [hstack, hs]
        rfl
      · exact hstackFrame i hi
    have hnone := select_none_of_raw_failure k F (BinaryArithmetic.toNat base) (by omega)
      hwidth hnodup hdistinct hfails
    refine ⟨hes, by rw [hes]; exact hclean 9 (by decide),
      by rw [hes]; exact hclean 12 (by decide), hnone, hfails, ?_⟩
    exact SparseBudget.leaf_occurrences_le_power (ExecCNF.formulaSet F) k
      (BinaryArithmetic.toNat base) (by omega) hM (formulaSet_width_le F hwidth) hnone
  · intro htrue
    obtain ⟨c, H, hp, h9, h12⟩ := hhit (hflag.symm.trans htrue)
    refine ⟨c, H, hp, hp.toPriority (by omega) hwidth hnodup hdistinct, ?_, ?_⟩
    · exact ((hstack 9).trans h9).trans (clause_words H)
    · exact ((hstack 12).trans h12).trans (body_words (selectedRaw F c H))

/-- Normalized node syntax has a uniform polynomial bound for fixed `k`.
The binary threshold word is charged separately, with its actual bit length. -/
theorem inputVolume_le_formulaBound (F : RawCNF n) (base : List Bool) (k : ℕ)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    inputVolume F base ≤ SparseCountProgram.formulaBound n k + base.length + 1 := by
  have h := SparseCountProgram.encodeBody_length_le F k hnodup hdistinct
    (formulaSet_width_le F hwidth)
  unfold inputVolume
  omega

theorem source_time_bound (F : RawCNF n) (base : List Bool) (k : ℕ)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    Selector.selectorCoefficient k * inputVolume F base ^ 4 + 1 ≤
      Selector.selectorCoefficient k *
        (SparseCountProgram.formulaBound n k + base.length + 1) ^ 4 + 1 :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (inputVolume_le_formulaBound F base k hwidth hnodup hdistinct) 4)) 1

theorem source_space_bound (F : RawCNF n) (base : List Bool) (k frameBound : ℕ)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    max ((Selector.selectorCoefficient k + 24) * inputVolume F base ^ 4) frameBound ≤
      max ((Selector.selectorCoefficient k + 24) *
        (SparseCountProgram.formulaBound n k + base.length + 1) ^ 4) frameBound :=
  max_le_max (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (inputVolume_le_formulaBound F base k hwidth hnodup hdistinct) 4)) le_rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement
