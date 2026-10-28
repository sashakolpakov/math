import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRun

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
open LeafParametersProgram

/-- Direct input-statistic values in the persistent metadata bank. -/
theorem exported_input_values (x : Input) (l : Fin 8 → ℕ) (a : Data)
    (h : Exported (Execute.guardedModel x l) a) :
    a.stacks 128=List.replicate x.ambient true ∧
    a.stacks 129=List.replicate x.factors true ∧
    BinaryArithmetic.toNat (a.stacks 723)=x.incidences ∧
    BinaryArithmetic.toNat (a.stacks 724)=x.freeCount ∧
    BinaryArithmetic.toNat (a.stacks 725)=x.occurrence ∧
    BinaryArithmetic.toNat (a.stacks 726)=x.factors := by
  have h0 : (Execute.guardedModel x l).val 0=x.ambient := Execute.guardedModel_input x l 0
  have h1 : (Execute.guardedModel x l).val 1=x.freeCount := Execute.guardedModel_input x l 1
  have h3 : (Execute.guardedModel x l).val 3=x.occurrence := Execute.guardedModel_input x l 3
  have h5 : (Execute.guardedModel x l).val 5=x.factors := Execute.guardedModel_input x l 5
  have h7 : (Execute.guardedModel x l).val 7=x.incidences := Execute.guardedModel_input x l 7
  exact ⟨by simpa [Exports.destination,Exports.unaryValues,h0] using h.1 0,
    by simpa [Exports.destination,Exports.unaryValues,h5] using h.1 1,
    by simpa [Exports.destination,Exports.binarySources,h7] using h.2 3,
    by simpa [Exports.destination,Exports.binarySources,h1] using h.2 4,
    by simpa [Exports.destination,Exports.binarySources,h3] using h.2 5,
    by simpa [Exports.destination,Exports.binarySources,h5] using h.2 6⟩

/-- The packing dimensions exported from the completed native parameter bank. -/
theorem exported_parameter_values (x : Input) (l : Fin 8 → ℕ) (a : Data)
    (h : Exported (Execute.guardedModel x l) a) :
    BinaryArithmetic.toNat (a.stacks 720)=(produce x).Q ∧
    BinaryArithmetic.toNat (a.stacks 721)=(produce x).r ∧
    BinaryArithmetic.toNat (a.stacks 722)=(produce x).epsilonDen ∧
    BinaryArithmetic.toNat (a.stacks 727)=(produce x).R := by
  have h18 : (Execute.guardedModel x l).val 18=(produce x).r := Execute.guardedModel_radius x l
  have h21 : (Execute.guardedModel x l).val 21=(produce x).Q :=
    (Execute.guardedModel_public x l 4).trans (Layout.model_core_values x l).2.2.2.2.1
  have h25 : (Execute.guardedModel x l).val 25=(produce x).epsilonDen :=
    (Execute.guardedModel_public x l 5).trans (Layout.model_core_values x l).2.2.2.2.2.1
  have h29 : (Execute.guardedModel x l).val 29=(produce x).R :=
    (Execute.guardedModel_public x l 6).trans (Layout.model_core_values x l).2.2.2.2.2.2.1
  exact ⟨by simpa [Exports.destination,Exports.binarySources,h21] using h.2 0,
    by simpa [Exports.destination,Exports.binarySources,h18] using h.2 1,
    by simpa [Exports.destination,Exports.binarySources,h25] using h.2 2,
    by simpa [Exports.destination,Exports.binarySources,h29] using h.2 7⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
