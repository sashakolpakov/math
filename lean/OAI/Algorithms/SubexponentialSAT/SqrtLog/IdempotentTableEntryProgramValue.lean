import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgramLookup

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open IdempotentProgram

def entryCode (i j k : ℕ) : Fin 6 :=
  if k < 3*(i/3+j/3) then 0
  else ((coefficientsAt (i%3+j%3))[k-3*(i/3+j/3)]?).getD 0

theorem coefficientsAt_value (a : ℕ) (ha : a ≤ 4) (n : ℕ) :
    codeValue (((coefficientsAt a)[n]?).getD 0) =
      if a < 3 then (if n = a then 1 else 0)
      else if a = 3 then
        (if n = 3 then 1 else 0) + (if n = 1 then -2 else 0) +
          (if n = 2 then 3 else 0)
      else
        (if n = 3 then 3 else 0) + (if n = 4 then 1 else 0) +
          (if n = 1 then -6 else 0) + (if n = 2 then 7 else 0) := by
  by_cases hn : n < 5
  · interval_cases a <;> interval_cases n <;> norm_num [coefficientsAt,codeValue]
  · have hnone : (coefficientsAt a)[n]? = none :=
      List.getElem?_eq_none (by rw [coefficientsAt_length]; omega)
    rw [hnone]
    interval_cases a <;> simp [codeValue,show n ≠ 0 by omega,
      show n ≠ 1 by omega,show n ≠ 2 by omega,show n ≠ 3 by omega,
      show n ≠ 4 by omega]

theorem entryCode_correct {t : ℕ} (i j k : Fin (3*t)) :
    codeValue (entryCode i.val j.val k.val) = hadicTable i j k := by
  have ha : i.val%3+j.val%3 ≤ 4 := by omega
  by_cases hk : k.val < 3*(i.val/3+j.val/3)
  · have h0 : k.val ≠ 3*(i.val/3+j.val/3)+(i.val%3+j.val%3) := by omega
    have h1 : k.val ≠ 3*(i.val/3+j.val/3)+1 := by omega
    have h2 : k.val ≠ 3*(i.val/3+j.val/3)+2 := by omega
    have h3 : k.val ≠ 3*(i.val/3+j.val/3+1) := by omega
    have h4 : k.val ≠ 3*(i.val/3+j.val/3+1)+1 := by omega
    simp [entryCode,hk,codeValue,hadicTable,atomInteger,h0,h1,h2,h3,h4]
  · rw [entryCode,ite_eq_right hk,coefficientsAt_value _ ha]
    have h0 : k.val-3*(i.val/3+j.val/3) = i.val%3+j.val%3 ↔
        k.val = 3*(i.val/3+j.val/3)+(i.val%3+j.val%3) := by omega
    have h1 : k.val-3*(i.val/3+j.val/3) = 1 ↔
        k.val = 3*(i.val/3+j.val/3)+1 := by omega
    have h2 : k.val-3*(i.val/3+j.val/3) = 2 ↔
        k.val = 3*(i.val/3+j.val/3)+2 := by omega
    have h3 : k.val-3*(i.val/3+j.val/3) = 3 ↔
        k.val = 3*(i.val/3+j.val/3+1) := by omega
    have h4 : k.val-3*(i.val/3+j.val/3) = 4 ↔
        k.val = 3*(i.val/3+j.val/3+1)+1 := by omega
    simp only [h0,h1,h2,h3,h4,hadicTable,atomInteger]

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
