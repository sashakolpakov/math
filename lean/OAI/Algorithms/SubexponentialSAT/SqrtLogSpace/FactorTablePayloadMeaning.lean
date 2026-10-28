import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryIncidenceSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblySource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeMaskDecode

/-! The unchanged actual specialized payload and its source witness predicate.
Execution and resource theorems remain in FactorTableNative. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes

def specializedRowPayload (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (mask : List Bool) : List Bool :=
  MomentsProgram.Product.bytes (MomentsProgram.Normalize.run 3 t M cache
    (HeadEvaluation.specializeEntries (Squarefree.decodeMask rows.length mask)
      (QueryProducerSpace.emittedSource t model M cache J N theta rows)) [])

/-- Meaning of a stored incidence payload. The low branch retains the actual
native source row witness; both branches expose a canonical scalar dictionary. -/
structure PayloadMeaning {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (j : ℕ) (payload : List Bool) : Prop where
  good : ∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
    TruncatedRingProgram.Good ∅ u J entries ∧ payload = MomentsProgram.Product.bytes entries
  source : if (s 574).getD j false then
    payload = Encoding.frame (originKey n) ++
      Encoding.frame (if (s 575).getD j false then s 548 else s 547)
    else ∃ xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)),
      xs.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f j
            (LayoutSourceRowsProgram.totalPackedSource p P) z)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
      payload = specializedRowPayload p.t p.model p.modulus p.cache J (p.R+1)
        theta (pairChoice xs (s 546)) (s 857)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
