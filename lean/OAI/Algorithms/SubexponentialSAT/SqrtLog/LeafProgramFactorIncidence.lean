import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyIncidenceCaller

namespace OAI.Algorithms

/-! The parsed factor ID is physically converted to the unary source index,
then the complete source-backed incidence service is invoked and reclaimed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram

theorem prepareIncidence_eval {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : Data) (width : List Bool) (frame : Fin 6 → List Bool)
    (hid : a.stacks 149=(Encoding.encodeNat f).reverse)
    (h556 : a.stacks 556=[]) (h359 : a.stacks 359=[])
    (hready : IncidenceReady p ps P J n f S B theta
      (projectState Incidence.callerRegisters id (FactorID.output a f)) width frame) :
    let staged := Incidence.staged (projectState Incidence.callerRegisters id (FactorID.output a f))
    ∃ (payload : ℕ → List Bool) (k : ℕ) (b : Data),
      (∀ j,j < n → (payload j).length ≤ incidenceBitsBound n J (d*baseWidth 3 p.t) ∧
        payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
          (sourceRowProperty p ps P n f) staged.stacks j (payload j)) ∧
      k ≤ 7*(f+1)+6+
        (incidenceWorkBound p (projectState Incidence.callerRegisters id (FactorID.output a f)) n J S B+1) ∧
      Eval prepareIncidence k a b ∧
      b.stacks=Function.update a.stacks 62 (Squarefree.Program.lookupRecords
        (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ())) := by
  dsimp only
  have hidrun := FactorID.command_eval a f hid h556 h359
  obtain ⟨payload,k,rf,hpayload,hk,he⟩ := incidence_caller_from_source p ps P J n f S B theta
    (FactorID.output a f) width frame hready
  refine ⟨payload,7*(f+1)+6+k,_,hpayload,Nat.add_le_add_left hk _,hidrun.seq he,?_⟩
  rw [incidenceWideOutput_stacks]
  funext i
  by_cases h62 : i=62
  · subst i; simp [incidenceOutput]
  by_cases hf : i=556
  · subst i; simp [incidenceOutput,h556]
  · simp [incidenceOutput,FactorID.output,h62,hf]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
