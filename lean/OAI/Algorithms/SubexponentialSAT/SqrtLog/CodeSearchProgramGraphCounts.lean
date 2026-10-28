import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphCountTail
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramBinaryWeight
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramWord

namespace OAI.Algorithms

/-! Fixed bit-code for one Walsh query up to the scalar inequalities: compute
all dot products mod2, count their support, and recognize the zero character. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

def extendPairState (base : State 8 16) (first second : List Bool) : ScanState :=
  ⟨base.regs,fun j => if h : j.val < 16 then base.stacks ⟨j.val,h⟩
    else if j = 16 then first else second⟩

private theorem pair_embed (base : State 8 16) (first second : List Bool) :
    embedState id matrixWordStacks (extendPairState base first second) base =
      extendPairState base first second := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendPairState,i.isLt]
  · intros; rfl
  · intros; rfl

private theorem pair_embed_result (initial final : State 8 16) (first second : List Bool) :
    embedState id matrixWordStacks (extendPairState initial first second) final =
      extendPairState final first second := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intro i; rfl
  · intro i; simp [extendPairState,i.isLt]
  · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
  · intro j hj
    have hnot : ¬j.val < 16 := by
      intro h; exact hj ⟨⟨j.val,h⟩,Fin.ext rfl⟩
    simp [extendPairState,hnot]

abbrev graphCountsCommand : Cmd 8 18 :=
  .seq (.call (ProgramLinking.liftProgram MatrixVectorProgram.matrixProgram id matrixWordStacks))
    graphCountTail

def graphCountsProgram := compiled graphCountsCommand 11 9

def graphCountsBudget (D r : ℕ) := MatrixVectorProgram.matrixBudget D r 2 + 10 * D + 10 * r + 9

theorem graphCounts_eval {r D : ℕ} (s : Fin D → Cayley.Cube r) (a : Cayley.Cube r)
    (regs : Fin 8 → Bool) (qbits Dbits : List Bool) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ graphCountsBudget D r ∧
      Eval graphCountsCommand n (extendPairState (matrixInput s a regs) qbits Dbits) next ∧
      next.regs 7 = decide (a ≠ 0) ∧
      next.stacks 9 = List.replicate (WalshExistence.parityWeight s a) true ∧
      next.stacks 16 = qbits ∧ next.stacks 17 = Dbits := by
  obtain ⟨nm,rm,hnm,htm⟩ := matrix_apply_trace s a regs
  have hm := eval_call_lifted MatrixVectorProgram.matrixProgram id matrixWordStacks
    (extendPairState (matrixInput s a regs) qbits Dbits)
    Function.injective_id (Fin.castAdd_injective _ _) htm
  rw [pair_embed,pair_embed_result] at hm
  let y := WalshExistence.parityProducts s a
  let ys := (List.ofFn y).map binaryCell
  let xs := (List.ofFn a).map binaryCell
  have hy : (extendPairState (matrixOutput s a rm) qbits Dbits).stacks 8 = framedCellStream ys :=
    scalarFrames_binary _
  have hx : (extendPairState (matrixOutput s a rm) qbits Dbits).stacks 12 = framedCellStream xs :=
    scalarFrames_binary _
  obtain ⟨nt,out,hnt,ht,hflag,hcount,h16,h17⟩ := graphCountTail_eval ys xs
    (extendPairState (matrixOutput s a rm) qbits Dbits) hy hx (by rfl) (by rfl)
  have hyw : cellWeight ys = WalshExistence.parityWeight s a := by
    rw [cellWeight_binary,List.map_ofFn,List.sum_ofFn]
    change (∑ i : Fin D,if y i ≠ 0 then 1 else 0) = _
    rw [← Finset.sum_filter]
    simp [y,WalshExistence.parityWeight]
  refine ⟨nm+nt,out,?_,hm.seq ht,?_,?_,h16,h17⟩
  · have hw : MatrixWordEncoding.width 2 = 2 := by
      norm_num [MatrixWordEncoding.width,SubexpLiftRing.baseWidth]
    rw [hw] at hnm
    have hyl : ys.length = D := by simp [ys]
    have hxl : xs.length = r := by simp [xs]
    rw [hyl,hxl] at hnt
    unfold graphCountsBudget
    omega
  · apply hflag.trans
    exact decide_eq_decide.mpr (not_congr (binary_weight_zero_iff a))
  · simpa only [hyw] using hcount

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
