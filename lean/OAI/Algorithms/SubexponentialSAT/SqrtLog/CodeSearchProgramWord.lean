import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramWordTail
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramRepresentation

namespace OAI.Algorithms

/-! A complete fixed-code test of one proposed short nonzero kernel word.
Matrix and word bytes, the row count, and the distance threshold are runtime
inputs. The protected stack 17 survives the call. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

def matrixWordStacks : Fin 16 → Fin 18 := Fin.castAdd 2

def extendMatrixState (base : State 8 16) (d : ℕ) (saved : List Bool) : ScanState :=
  ⟨base.regs, fun j => if h : j.val < 16 then base.stacks ⟨j.val,h⟩
    else if j = 16 then List.replicate d true else saved⟩

abbrev wordCommand : Cmd 8 18 :=
  .seq (.call (ProgramLinking.liftProgram MatrixVectorProgram.matrixProgram
    id matrixWordStacks)) wordTailCommand

def wordProgram := compiled wordCommand 11 10

def wordBudget (t D : ℕ) :=
  MatrixVectorProgram.matrixBudget t D 2 + wordTailBudget t D

def wordRejects {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) : Prop :=
  SparseCode.IsCodeword Q x ∧ x ≠ 0 ∧ SparseCode.weight x < d

instance {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) : Decidable (wordRejects Q x d) := by
  unfold wordRejects SparseCode.IsCodeword
  infer_instance

private theorem extend_embed (base : State 8 16) (d : ℕ) (saved : List Bool) :
    embedState id matrixWordStacks (extendMatrixState base d saved) base =
      extendMatrixState base d saved := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendMatrixState, i.isLt]
  · intros; rfl
  · intros; rfl

private theorem extend_embed_result (initial final : State 8 16) (d : ℕ)
    (saved : List Bool) :
    embedState id matrixWordStacks (extendMatrixState initial d saved) final =
      extendMatrixState final d saved := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendMatrixState, i.isLt]
  · intro j hj
    exact False.elim (hj ⟨j,rfl⟩)
  · intro j hj
    have hnot : ¬ j.val < 16 := by
      intro h
      exact hj ⟨⟨j.val,h⟩, Fin.ext rfl⟩
    simp [extendMatrixState, hnot]

theorem word_eval {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (regs : Fin 8 → Bool)
    (saved : List Bool) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ wordBudget t D ∧
      Eval wordCommand n (extendMatrixState (matrixInput Q x regs) d saved) next ∧
      next.regs 7 = decide (wordRejects Q x d) ∧ next.stacks 17 = saved := by
  obtain ⟨nm, rm, hnm, htm⟩ := matrix_apply_trace Q x regs
  have hm := eval_call_lifted MatrixVectorProgram.matrixProgram id matrixWordStacks
    (extendMatrixState (matrixInput Q x regs) d saved)
    Function.injective_id (Fin.castAdd_injective _ _) htm
  rw [extend_embed, extend_embed_result] at hm
  let y : Fin t → SparseCode.F3 := fun i => ∑ j, Q i j * x j
  let ys := (List.ofFn y).map ternaryCell
  let xs := (List.ofFn x).map ternaryCell
  have hy : (extendMatrixState (matrixOutput Q x rm) d saved).stacks 8 =
      framedCellStream ys := by
    change scalarFrames (List.ofFn y) = _
    exact scalarFrames_ternary _
  have hx : (extendMatrixState (matrixOutput Q x rm) d saved).stacks 12 =
      framedCellStream xs := by
    change scalarFrames (List.ofFn x) = _
    exact scalarFrames_ternary _
  obtain ⟨nt, out, hnt, ht, hflag, hsave⟩ := wordTail_eval ys xs d
    (extendMatrixState (matrixOutput Q x rm) d saved) hy hx (by rfl) (by rfl) (by rfl)
  have hxw : cellWeight xs = SparseCode.weight x := by
    rw [cellWeight_ternary, List.map_ofFn, List.sum_ofFn, SparseCode.weight_eq_sum]
    rfl
  have hyw : cellWeight ys = SparseCode.weight y := by
    rw [cellWeight_ternary, List.map_ofFn, List.sum_ofFn, SparseCode.weight_eq_sum]
    rfl
  refine ⟨nm + nt, out, ?_, hm.seq ht, ?_, hsave⟩
  · have hwidth : MatrixWordEncoding.width 3 = 2 := by
      norm_num [MatrixWordEncoding.width, SubexpLiftRing.baseWidth]
    rw [hwidth] at hnm
    have hyl : ys.length = t := by simp [ys]
    have hxl : xs.length = D := by simp [xs]
    rw [hyl, hxl] at hnt
    unfold wordBudget
    omega
  · rw [hxw, hyw] at hflag
    have hy0 : SparseCode.weight y = 0 ↔ SparseCode.IsCodeword Q x :=
      ternary_product_weight_zero Q x
    have hx0 : SparseCode.weight x ≠ 0 ↔ x ≠ 0 :=
      not_congr (SparseCode.weight_eq_zero_iff x)
    apply hflag.trans
    exact decide_eq_decide.mpr (and_congr hy0 (and_congr hx0 Iff.rfl))

theorem word_runsIn {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (regs : Fin 8 → Bool) (saved : List Bool) :
    ∃ next : ScanState, RunsIn wordProgram (wordBudget t D)
      ((extendMatrixState (matrixInput Q x regs) d saved).withPC (some wordProgram.entry))
      (next.withPC none) ∧ next.regs 7 = decide (wordRejects Q x d) ∧
      next.stacks 17 = saved := by
  obtain ⟨n, next, hn, he, hf, hs⟩ := word_eval Q x d regs saved
  exact ⟨next, ⟨n + 1, hn, compiled_halt_trace he 11 10⟩, hf, hs⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
