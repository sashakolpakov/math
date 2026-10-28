import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeCache

namespace OAI.Algorithms

/-! Close the only service premise of the head loop using the actual entry
machine and the bootstrap's produced caches. All budgets are explicit. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def Inputs.valid (s : Inputs) (j v : ℕ) : Prop := j < s.D ∧ v < s.n

theorem initial_contract (s : Inputs) (a : LeafHeadSetupProgram.Data) (ha : Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words) :
    LayoutMatrixProgram.EntryContract entry (matrixBase (start s a ra rd rc words))
      s.valid s.relation s.columnTime s.columnLength := by
  apply LayoutFiberSumProgram.nativeEntryContract s.packing words s.width s.power
    s.height s.R s.node (matrixBase (start s a ra rd rc words)) s.plans s.valid
    s.size s.lookupTime s.offset s.columnTime s.columnLength
  · simpa [unary] using hw.1
  · exact hw.2.1
  · simpa [unary] using hw.2.2
  · exact s.power_signed
  · exact s.power_total
  · exact s.power_value
  · exact s.width_node
  · exact s.height_le
  · have := s.node.isLt; omega
  · exact start_cache s a ha ra rd rc words
  · intro j v hv
    exact matrixBase_fiberReady (start s a ra rd rc words) (fun _=>false)
      (LayoutFiberSumProgram.unary j) []
  · simpa [matrixBase,LayoutMatrixProgram.bankPort,Inputs.metadata] using
      (start_low s a ra rd rc words 135 (by decide)).trans ha.metadata
  · simpa [matrixBase,LayoutMatrixProgram.bankPort] using
      (start_low s a ra rd rc words 136 (by decide)).trans ha.plans
  · exact start_size s a ha ra rd rc words hw
  · exact s.plans_length
  · unfold Inputs.size; omega
  · exact fun j v hv=>hv.1
  · exact s.metadata_bound
  · exact s.lookup_bound
  · exact fun j v hv=>s.column_time_bound v hv.2
  · exact fun j v hv=>s.column_length_bound v
  · exact fun j v hv=>s.column_mass_bound v hv.2

theorem node_contract (s : Inputs) (a : LeafHeadSetupProgram.Data) (ha : Ready s a) :
    NodeEntry entry a s.n s.N (s.Q*s.r) s.r s.node.val s.records s.rows s.low
      s.height (unary s.R) s.width s.valid s.relation s.columnTime s.columnLength := by
  apply nodeEntry_of_initial
  exact fun ra rd rc words hw=>initial_contract s a ha ra rd rc words hw

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
