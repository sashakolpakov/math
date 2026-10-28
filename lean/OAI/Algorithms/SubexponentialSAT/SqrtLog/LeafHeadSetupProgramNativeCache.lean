import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeInputs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBootPolynomial

namespace OAI.Algorithms

/-! The native entry cache is the actual output of the paid node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open RowSelectionProgram

def start (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :=
  nodeStart a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

theorem start_low (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) : (start s a ra rd rc words).stacks i=a.stacks i := by
  apply nodeStart_frame
  · constructor
    · left; exact hi
    · intro h; have hh := congrArg Fin.val h; simp [temporary] at hh; omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega

theorem start_positive (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 640=words.flatten := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (640:Fin 768)≠665 by decide),
    Function.update_of_ne (show (640:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 640 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_positive _ _ _ _ _ _ _ _ _ _ _

theorem start_negative (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 641=List.replicate (s.R*s.width.length) false := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (641:Fin 768)≠665 by decide),
    Function.update_of_ne (show (641:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 641 (by decide) (by decide) (by decide) (by decide)]
  simpa [unary] using bootState_negative a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

theorem start_denominator (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 642=s.power.1 := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (642:Fin 768)≠665 by decide),
    Function.update_of_ne (show (642:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 642 (by decide) (by decide) (by decide) (by decide)]
  simpa [unary,Inputs.power] using bootState_denominator a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

theorem start_cache (s : Inputs) (a : LeafHeadSetupProgram.Data) (ha : Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    LayoutProgram.EntryBank.CacheWords (r:=s.r)
      (LayoutFiberSumProgram.matrixBase (matrixBase (start s a ra rd rc words)) 0)
      (LayoutProgramScalar.FromCounts.unsignedSaved words s.width s.power s.R s.height) s.node := by
  have hf := start_low s a ra rd rc words
  constructor
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using start_positive s a ra rd rc words
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using start_negative s a ra rd rc words
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using (hf 140 (by decide)).trans ha.width
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using start_denominator s a ra rd rc words
  · rfl
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using (hf 138 (by decide)).trans ha.order
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort,LayoutProgramScalar.FromCounts.unsignedSaved]
      using (hf 139 (by decide)).trans ha.height
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 130 (by decide)).trans ha.colors
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 131 (by decide)).trans ha.nodes
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 307 (by decide)).trans ha.node
  · simpa [LayoutFiberSumProgram.matrixBase,LayoutMatrixProgram.entryState,matrixBase,
      LayoutMatrixProgram.bankPort] using (hf 132 (by decide)).trans ha.wordWidth

theorem start_size (s : Inputs) (a : LeafHeadSetupProgram.Data) (ha : Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words)
    (i : Fin 256) (hi : i.val < 212) :
    (matrixBase (start s a ra rd rc words) (LayoutMatrixProgram.bankPort i)).length ≤ s.size := by
  by_cases hlo : i.val < 200
  · rw [matrixBase_entry_low _ i hlo]; simp
  have hc : i=200 ∨ i=201 ∨ i=202 ∨ i=203 ∨ i=204 ∨ i=205 ∨
      i=206 ∨ i=207 ∨ i=208 ∨ i=209 ∨ i=210 ∨ i=211 := by omega
  have hf := start_low s a ra rd rc words
  have hflat : words.flatten.length=s.R*s.width.length := by
    rw [cacheWords_flat_length words s.width.length hw.2.1,hw.1]
    simp [unary]
  have ht : s.node.val < s.Q := s.node.isLt
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change ((start s a ra rd rc words).stacks 135).length ≤ s.size
    rw [(hf 135 (by decide)).trans ha.metadata]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 136).length ≤ s.size
    rw [(hf 136 (by decide)).trans ha.plans]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 640).length ≤ s.size
    rw [start_positive,hflat]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 641).length ≤ s.size
    rw [start_negative,List.length_replicate]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 140).length ≤ s.size
    rw [(hf 140 (by decide)).trans ha.width]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 642).length ≤ s.size
    rw [start_denominator]
    simp only [Inputs.power,LayoutProgram.IntegerCache.denominatorWord,List.length_append,List.length_replicate,List.length_singleton]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 138).length ≤ s.size
    rw [(hf 138 (by decide)).trans ha.order]
    simp only [unary,List.length_replicate]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 139).length ≤ s.size
    rw [(hf 139 (by decide)).trans ha.height]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 130).length ≤ s.size
    rw [(hf 130 (by decide)).trans ha.colors]
    simp only [unary,List.length_replicate]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 131).length ≤ s.size
    rw [(hf 131 (by decide)).trans ha.nodes]
    simp only [unary,List.length_replicate]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 307).length ≤ s.size
    rw [(hf 307 (by decide)).trans ha.node]
    simp only [unary,List.length_replicate]
    unfold Inputs.size
    omega
  · change ((start s a ra rd rc words).stacks 132).length ≤ s.size
    rw [(hf 132 (by decide)).trans ha.wordWidth]
    simp only [unary,List.length_replicate]
    unfold Inputs.size
    omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
