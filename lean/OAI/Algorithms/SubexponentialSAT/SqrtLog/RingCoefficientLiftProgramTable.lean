import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableData

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram

theorem modelCoefficientBits (t : ℕ) {d : ℕ} (a : RingModel.Data d) :
    RingProgramTable.wordBits
        (List.Vector.ofFn (RingProgram.liftCoefficientsRun t a.coefficients).1).val =
      RingProgram.flat (RingProgram.liftCoefficientsRun t a.coefficients).1 := by
  change (((List.Vector.ofFn (RingProgram.liftCoefficientsRun t a.coefficients).1).toList).map
    Subtype.val).flatten = _
  rw [List.Vector.toList_ofFn,List.map_ofFn]
  rfl

/-- The vector below is definitionally `RingProgramTable.modelCoefficients t a`
when that model wrapper is imported. This byte bridge needs only the data ABI.
The native search adapter provides exactly the polynomial bytes expected
by the native structure-table generator, with both loops paid. -/
theorem model_search_trace (t : ℕ) (ht : 0 < t) {d : ℕ} (a : RingModel.Data d)
    (s : SearchData) (hready : SearchReady s)
    (hinput : s.stacks 13=IrreducibleSearchProgram.coefficientArray (List.ofFn a.coefficients))
    (hwidth : (s.stacks 12).length=SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ e : SearchData, Trace searchProgram (d*(28*t+14)+7)
      (s.withPC (some searchProgram.entry)) (e.withPC none) ∧
      e.stacks=Function.update (Function.update s.stacks 13 []) 21
        (RingProgramTable.wordBits
        (List.Vector.ofFn (RingProgram.liftCoefficientsRun t a.coefficients).1).val) := by
  rw [modelCoefficientBits]
  exact searchProgram_trace t ht a.coefficients s hready hinput hwidth

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

end OAI.Algorithms
