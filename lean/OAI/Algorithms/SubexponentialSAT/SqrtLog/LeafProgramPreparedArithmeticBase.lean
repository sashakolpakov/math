import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeNode

namespace OAI.Algorithms

/-! The shared arithmetic context of the node and reconstruction programs is
formed from the actual ring producer, using its literal width and degree words. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
noncomputable section

variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (J : ℕ) (hJ : 0 < J)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)

def nodeArithmeticOfProduced : Residual.Native.NodeArithmetic where
  t := m.val 33
  d := m.val 34
  u := m.val 33
  J := J
  modulus := M
  cache := cache
  canonicalZero := hp.caches.canonical
  table := HornerProgram.modelTable (m.val 33)
    (IrreducibleSearch.data hd) M cache
  degree := e.stacks 204
  width := e.stacks 202
  degreeLength := hp.caches.degree
  widthLength := hp.caches.width
  positiveU := ht
  positiveJ := hJ
  one := (RingProgram.modelProgram (m.val 33)
    (IrreducibleSearch.data hd) M cache).oneRun.1
  zero := (RingProgram.modelProgram (m.val 33)
    (IrreducibleSearch.data hd) M cache).zeroRun.1

theorem nodeArithmeticOfProduced_words (hj : m.val 42=J) :
    e.stacks 194=(nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).modulus.bits ∧
    e.stacks 201=RingTriple.tableEncoding (nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).table ∧
    e.stacks 202=(nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).width ∧
    e.stacks 203=(nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).cache.zero.val ∧
    e.stacks 204=(nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).degree ∧
    e.stacks 212=List.replicate (nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).u true ∧
    e.stacks 243=List.replicate (nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).J true ∧
    e.stacks 207=RingProgram.flat (nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).one ∧
    e.stacks 280=RingProgram.flat (nodeArithmeticOfProduced m ht hd J hJ M cache half e hp).zero := by
  refine ⟨hp.caches.modulus,hp.native.table,rfl,hp.caches.scalarZero,rfl,hp.caches.precision,?_,
    hp.caches.fullOne_model,hp.caches.fullZero_model⟩
  simpa only [nodeArithmeticOfProduced,hj] using hp.jetOrder


end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
