import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankUniversal

namespace OAI.Algorithms

/-! Uniform polynomial resource bounds for the concrete universal source
branch. Typed table entries contribute their actual d*B bit width. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

def sourceWorkspace (p : Parameters r Q d) (S : ℕ) : ℕ :=
  S+Q*(d*SubexpLiftRing.baseWidth 3 p.t)+UniversalRowSourceBound.indicesBound Q

def universalBudget (p : Parameters r Q d) (S : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  LayoutSourceValuesProgram.Native.tableBudget p.aWord.length p.R p.width.length
    (pairLength p.power) p.t d u y+
  (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
    UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
  14*S+224*sourceWorkspace p S+UniversalRowSourceBound.sourceBound (sourceWorkspace p S)+281

def uniformBudget (p : Parameters r Q d) (S : ℕ) : ℕ :=
  LayoutSourceValuesProgram.Native.polynomialBudget r Q p.aWord.length p.R p.width.length
    (pairLength p.power) p.t d+
  (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
    UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
  14*S+224*sourceWorkspace p S+UniversalRowSourceBound.sourceBound (sourceWorkspace p S)+281

theorem universalBudget_le (p : Parameters r Q d) (S : ℕ) (u y : UniversalType r Q 1) :
    universalBudget p S u y ≤ uniformBudget p S := by
  have hh := LayoutSourceValuesProgram.Native.tableBudget_polynomial
    p.aWord.length p.R p.width.length (pairLength p.power) p.t d u y
  unfold universalBudget uniformBudget
  omega

private theorem bits_length (p : Parameters r Q d) (codes : Fin Q → ModelCode p.t d) :
    (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten.length=Q*(d*SubexpLiftRing.baseWidth 3 p.t) := by
  rw [List.length_flatten,List.map_ofFn]
  have hf : (List.length ∘ fun i=>RingProgram.flat (codes i))=
      fun _ : Fin Q=>d*SubexpLiftRing.baseWidth 3 p.t := by
    funext i
    exact RingProgram.flat_length _
  rw [hf]
  simp

private theorem indices_length (u y : UniversalType r Q 1) :
    (nativeIndices u y).length ≤ UniversalRowSourceBound.indicesBound Q := by
  rw [nativeIndices_eq,nativePositions_eq]
  exact SourceTyped.indices_length_le _

theorem nativeBudget_le (p : Parameters r Q d) (S : ℕ) (a : Data)
    (codes : Fin Q → ModelCode p.t d) (u y : UniversalType r Q 1)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (hS : ∀ j,(a.stacks j).length ≤ S) (hQ : Q ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    nativeBudget p S a codes u y ≤ universalBudget p S u y := by
  let bits := (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
  let idx := nativeIndices u y
  let z := branchState a (fun _=>false) bits idx
  let B := S+Q*(d*SubexpLiftRing.baseWidth 3 p.t)+idx.length
  have hsB : S ≤ B := by dsimp [B]; omega
  have hBS : B ≤ sourceWorkspace p S := by
    have hi := indices_length u y
    dsimp [B,idx,sourceWorkspace]
    omega
  have hz : ∀ j,(z.stacks j).length ≤ B := by
    have hh := branch_length_le a (fun _=>false) bits idx h23 h24 S hS
    simpa only [bits,bits_length] using hh
  let ts := SourceTyped.tables RingProgram.flat codes p.inverse p.negative p.difference
  have hvalid := SourceTyped.tables_valid RingProgram.flat codes p.inverse p.negative p.difference
    p.ringWidth p.rowWidth (fun c=>(RingProgram.flat_length c).trans p.hringWidth.symm) p.hrowWidth
    (SubexpRowInterpolation.mismatchPositions (fun v=>v.head) (u.slot 0) y)
  have hdelta : (deltaWord z).length ≤ sourceWorkspace p S := by
    unfold deltaWord
    split_ifs <;> exact (hz _).trans hBS
  have hE := UniversalRowSourceBound.source_bound_le ts p.ringWidth p.rowWidth
    (nativePositions u y) (deltaWord z) (z.stacks 47) (z.stacks 313) (z.stacks 314)
    (sourceWorkspace p S) (by simpa only [nativePositions_eq] using hvalid)
    (by rw [nativePositions_eq]; exact (SourceTyped.positions_length_le _).trans (hQ.trans (hsB.trans hBS)))
    (by intro i hi; rw [nativePositions_eq] at hi
        exact (SourceTyped.positions_value_le _ i hi).trans (hQ.trans (hsB.trans hBS)))
    (hW.trans (hsB.trans hBS)) (hRW.trans (hsB.trans hBS)) hdelta
    ((hz 47).trans hBS) ((hz 313).trans hBS) ((hz 314).trans hBS)
  have hf := finishBound_le ts p.ringWidth p.rowWidth (nativePositions u y) z B
    (UniversalRowSourceBound.sourceBound (sourceWorkspace p S)) hz hE.1
  have ht := stageTypes_cost_le a S hS
  dsimp [nativeBudget,universalBudget]
  change Staging.cost 0 1 stageTypesOps a+_+_+finishBound ts _ _ _ z B ≤ _
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
