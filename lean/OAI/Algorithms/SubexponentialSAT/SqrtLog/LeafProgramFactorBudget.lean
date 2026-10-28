import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorHash
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorMarked

namespace OAI.Algorithms

/-! Names for the measured complete factor-branch bounds. The source and
incidence costs remain part of these expressions. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram

noncomputable def hashBranchBudget {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ctx : Context 3 p.t n d) (f S B : ℕ)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (b : ℕ) (a : Data) (payload : ℕ → List Bool)
    (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)) : ℕ :=
  let entries := HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()
  let ws := HashInputProgram.Expansion.weightedRow p.t d source terms
  7*(f+1)+6+
    (incidenceWorkBound p (projectState Incidence.callerRegisters id (FactorID.output a f)) n ctx.J S B+1)+
    (9*(a.stacks 154).length+10+
      HashInputProgram.Loop.uniformBudget p.t (d-1) b (a.stacks 707)
        (HashInputProgram.Expansion.encodedClauses source) terms.length+
      FactorServices.indicatorBudget ctx minus one incidence entries ws digits+
      (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
        2*(Squarefree.Program.lookupRecords entries).length+6+
        productBudget 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
          (Indicator.result ctx minus one incidence ws digits)))

noncomputable def markedBranchBudget {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ctx : Context 3 p.t n d) (f S B : ℕ)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (ls : List (SAT.Literal (Fin n))) (a : Data) (payload : ℕ → List Bool)
    (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)) : ℕ :=
  let entries := HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()
  7*(f+1)+6+
    (incidenceWorkBound p (projectState Incidence.callerRegisters id (FactorID.output a f)) n ctx.J S B+1)+
    (9*(a.stacks 154).length+8+
      (FactorServices.clauseBudget ctx minus one incidence entries ls+
        (2*(Squarefree.Program.lookupRecords entries).length+3+
          productBudget 3 p.t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed
            (FactorServices.clauseResult ctx minus one incidence ls))))

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
