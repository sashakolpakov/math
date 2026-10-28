import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources

/-! Exact current-query mask and attained counter semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

/-- This set is derived from the current marked scope rows, with the original
ambient dimension. Its physical mask is the one produced by the frontend. -/
def highSet (q : LeafQueryFrontend.Query) : Finset (Fin (BinaryArithmetic.toNat q.ambient)) :=
  HighIncidence.high
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.suppliedScope (BinaryArithmetic.toNat q.ambient) q.scopeRows)
    ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.mass q.scopeRows *
      EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient)) ⌈/⌉ BinaryArithmetic.toNat q.ambient)

theorem physical_high_mask (q : LeafQueryFrontend.Query) :
    LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)=
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask (highSet q) := by
  exact OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.physical_mask _ _ _

theorem high_mask_count (q : LeafQueryFrontend.Query) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.trueCount
      (LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))=(highSet q).card := by
  exact OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.highPrefix_count_eq_card _ _ _

theorem high_card_le (q : LeafQueryFrontend.Query) (hv : q.Valid) :
    (highSet q).card≤BinaryArithmetic.toNat q.ambient /
      EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) := by
  rw [← high_mask_count]
  apply OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.computed_high_dimension_rawMass
  · exact hv.2.1
  · exact lt_of_lt_of_le (by decide : 0<2) (EarlyThreshold.threshold_ge_two _)

theorem initialized_current_counter (q : LeafQueryFrontend.Query) (a : Data) (rf : Fin 2 → Bool)
    (hm : a.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) :
    (HighCountSeed.initialized a rf).stacks 789=
      Encoding.encodeList id (List.replicate (highSet q).card [false]) := by
  rw [HighCountSeed.initialized_counter,hm,high_mask_count]

/-- The attained odometer's retained word has polynomial length, even though
the number of high assignments it visits can be exponential. -/
theorem initialized_current_counter_length (q : LeafQueryFrontend.Query) (a : Data) (rf : Fin 2 → Bool)
    (hm : a.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) :
    ((HighCountSeed.initialized a rf).stacks 789).length≤4*BinaryArithmetic.toNat q.ambient+1 := by
  rw [HighCountSeed.initialized_counter_length,hm,high_mask_count]
  have h := Finset.card_le_univ (highSet q)
  simp only [Fintype.card_fin] at h
  omega

theorem result_high_mask (q : LeafQueryFrontend.Query) (a : Data) (b : LeafProgram.Query.Data)
    (hm : b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) :
    (result a b).stacks 338=
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask (highSet q) := by
  rw [show (338 : Fin 896)=stackMap 338 from rfl,result_stack,hm,physical_high_mask]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
