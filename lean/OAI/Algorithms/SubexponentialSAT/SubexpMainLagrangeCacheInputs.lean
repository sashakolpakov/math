import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCachePorts
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheSetup
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheContext
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeInversePrelude

namespace OAI.Algorithms

/-! The Lagrange producer's typed inputs follow from the actual Main cache
setup result.  No prepared-ring dictionary is an additional caller input. -/

namespace SubexponentialSAT.SubexpMainLagrangeCache

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation)
open SubexpLiftRing SubexpQuarticRing

def targetData (p D : ℕ) [Fact p.Prime] : SubexpSelectedConversions.Prepared p D :=
  SubexpPreparedQuarticSetup.preparedData p D
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)

theorem setupFlat_eq_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpPreparedQuarticSetup.flat a = SubexpFlatAdd.encode a :=
  (show SubexpPreparedQuarticSetup.flat a = SubexpQuarticFlatMul.flat a from rfl).trans
    (SubexpConvolutionPair.flat_eq_encode a)

theorem inputs_valid {er es : ℕ} {alloc : Allocation es} {a e : MainState er es}
    (p D : ℕ) [Fact p.Prime] (h : SubexpMainCacheSetup.Result alloc a e p D)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p ^ 4 - 2) :
    SubexpLagrangeCacheContext.Valid p (D + 1) (targetData p D).modulus (sourceInputs e)
      (targetData p D).reduction (targetData p D).zero (targetData p D).one
      (SubexpPreparedQuarticSetup.minusOne p (D + 1)) := by
  constructor
  · change CounterPrograms.value (e.stacks (persistent es 6)) = p
    rw [CounterPrograms.value_eq_toNat, h.prime]
    exact hp
  · exact h.target 0
  · have hw := congrArg List.length (h.target 1)
    exact hw.trans (SubexpPreparedQuarticPrelude.widthWord_length p (D + 1))
  · exact h.target 2
  · exact (h.target 4).trans (setupFlat_eq_encode _)
  · exact h.target 5
  · rw [← setupFlat_eq_encode]
    exact SubexpPreparedRingStaging.bankWords_zero p D
      (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
      (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)
  · change CounterPrograms.value (e.stacks (persistent es 22)) = D + 1
    rw [CounterPrograms.value_eq_toNat, h.precision]
    exact hprecision
  · change BinaryArithmetic.toNat (e.stacks (persistent es 29)) = p ^ 4 - 2
    rw [h.exponent]
    exact hexp

theorem targetData_reduction (p D : ℕ) [Fact p.Prime] :
    (targetData p D).reduction.map (wordValue p (D + 1)) =
      reductionData (QuarticSearch.liftedCoefficients p (D + 1)) :=
  (targetData p D).reduction_spec

theorem targetData_zero (p D : ℕ) [Fact p.Prime] :
    SubexpLagrangeInverseCall.denote p (D + 1) (targetData p D).zero = 0 :=
  (targetData p D).zero_spec

theorem targetData_one (p D : ℕ) [Fact p.Prime] :
    SubexpLagrangeInverseCall.denote p (D + 1) (targetData p D).one = 1 :=
  (targetData p D).one_spec

theorem targetData_minusOne (p D : ℕ) [Fact p.Prime] :
    wordValue p (D + 1) (SubexpPreparedQuarticSetup.minusOne p (D + 1)) = -1 :=
  SubexpPreparedQuarticSetup.minusOne_value p (D + 1)

end SubexponentialSAT.SubexpMainLagrangeCache

end OAI.Algorithms
