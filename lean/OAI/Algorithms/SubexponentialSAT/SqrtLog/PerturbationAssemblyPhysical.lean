import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyIncidenceCaller
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReady

namespace OAI.Algorithms

/-! A single physical metadata invariant supplies every actual source call.
The final caller has no source execution, prepared table or evaluated beta
as a premise. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpSetupStorage
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

theorem incidenceReady_of_physical {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a : OuterData)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n)
    (h62 : a.stacks 62=[]) (htmp : a.stacks 684=[])
    (hbase : WordBound B (LeafProgram.Incidence.staged a))
    (hsize : sourceCallWordBound B n (incidenceBitsBound n J (d*baseWidth 3 p.t)) ≤ S)
    (hn : n ≤ S) (hf : f ≤ S) (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hphysical : LeafProgram.SourceReady.Input p ps P (LeafProgram.Incidence.staged a) 0 n f S) :
    IncidenceReady p ps P J n f S B theta a
      (LeafProgram.SourceReady.rawLow (LeafProgram.Incidence.staged a) 10) (fun _=>[]) := by
  refine ⟨h,h62,htmp,hbase,hsize,hn,hf,hplans,?_⟩
  intro j hj acc hacc hlow regs
  have hs : ∀ i,((sourceCallData (LeafProgram.Incidence.staged a).stacks j acc regs).stacks i).length ≤ S := by
    intro i
    exact (sourceCall_wordBound _ B n (incidenceBitsBound n J (d*baseWidth 3 p.t))
      j acc hbase hj hacc i).trans hsize
  have hi := sourceInput_at_call p ps P (LeafProgram.Incidence.staged a) 0 n f S j acc regs hphysical hs
  have hw : LeafProgram.SourceReady.rawLow
      (sourceCallData (LeafProgram.Incidence.staged a).stacks j acc regs) 10=
      LeafProgram.SourceReady.rawLow (LeafProgram.Incidence.staged a) 10 := by
    exact sourceCallData_frame _ j acc regs _ (by decide) (by decide) (by decide)
  refine ⟨?_,hi.call_bounds.1,hi.call_bounds.2⟩
  simpa only [hw] using hi.native

theorem incidence_caller_physical {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a : State 40 768)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta
      (projectState LeafProgram.Incidence.callerRegisters id a) n)
    (h62 : a.stacks 62=[]) (htmp : a.stacks 684=[])
    (hbase : WordBound B (LeafProgram.Incidence.staged
      (projectState LeafProgram.Incidence.callerRegisters id a)))
    (hsize : sourceCallWordBound B n (incidenceBitsBound n J (d*baseWidth 3 p.t)) ≤ S)
    (hn : n ≤ S) (hf : f ≤ S) (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hphysical : LeafProgram.SourceReady.Input p ps P
      (LeafProgram.Incidence.staged (projectState LeafProgram.Incidence.callerRegisters id a)) 0 n f S) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ incidenceBitsBound n J (d*baseWidth 3 p.t) ∧
        payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
          (sourceRowProperty p ps P n f)
          (LeafProgram.Incidence.staged (projectState LeafProgram.Incidence.callerRegisters id a)).stacks
          j (payload j)) ∧
      k ≤ incidenceWorkBound p (projectState LeafProgram.Incidence.callerRegisters id a) n J S B+1 ∧
      Eval LeafProgram.Incidence.caller k a
        (incidenceWideOutput a rf (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries
            (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))) := by
  exact incidence_caller_from_source p ps P J n f S B theta a _ _
    (incidenceReady_of_physical p ps P J n f S B theta
      (projectState LeafProgram.Incidence.callerRegisters id a) h h62 htmp hbase hsize hn hf hplans hphysical)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
