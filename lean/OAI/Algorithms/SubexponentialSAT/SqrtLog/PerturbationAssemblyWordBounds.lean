import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelOuter

namespace OAI.Algorithms

/-! Every concrete source-call input has an explicit word bound, including
the growing table accumulator and the freshly encoded original literal ID. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

def sourceCallWordBound (B n L : ℕ) : ℕ := B+n+n*literalRecordBound n L+1

theorem sourceCall_wordBound (s : OuterStore) (B n L j : ℕ) (acc : List Bool)
    (hbase : ∀ i,(s i).length ≤ B) (hj : j < n)
    (hacc : acc.length ≤ n*literalRecordBound n L) :
    ∀ i,((Function.update (literalReady s (List.replicate j true) acc)
      555 (Encoding.encodeNat j)) i).length ≤ sourceCallWordBound B n L := by
  intro i
  by_cases h555 : i=555
  · subst i
    simp only [Function.update_same,Encoding.encodeNat,List.length_append,
      List.length_replicate,List.length_singleton]
    unfold sourceCallWordBound
    omega
  by_cases h569 : i=569
  · subst i
    simpa [literalReady,sourceCallWordBound] using
      hacc.trans (by omega : n*literalRecordBound n L ≤ B+n+n*literalRecordBound n L+1)
  by_cases h573 : i=573
  · subst i
    simp [literalReady,sourceCallWordBound]
    omega
  simp only [literalReady,Function.update_of_ne h555,Function.update_of_ne h569,
    Function.update_of_ne h573]
  have hi := hbase i
  unfold sourceCallWordBound
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
