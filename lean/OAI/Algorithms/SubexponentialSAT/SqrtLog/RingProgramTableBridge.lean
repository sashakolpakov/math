import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramService

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem vectorRecords_flat {B d : ℕ} (v : List.Vector (Word B) d) :
    (List.ofFn (fun i => (v.get i).val)).flatten = wordBits v.val := by
  change (List.ofFn ((Subtype.val : Word B → List Bool) ∘ v.get)).flatten = _
  rw [← List.map_ofFn, listOfFn_get]
  rfl

private theorem powerRecords_succ {B d : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    RingTableLayout.powerRecords P (n+1) =
      List.ofFn (fun i => (P 0 i).val) ++ RingTableLayout.powerRecords (fun j => P (j+1)) n := by
  simp only [RingTableLayout.powerRecords, List.ofFn_succ, List.flatten_cons, Fin.val_zero,
    Fin.val_succ]

/-- The native power accumulator is exactly the forward record layout consumed
by the indexed table-layout machine. -/
theorem generatedBits_eq_powerRecords (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (n : ℕ) (v : VectorData (baseWidth p t) d) :
    wordBits v.coefficients.val ++ generatedBits p t M zeroWord minusOne c n v =
      (RingTableLayout.powerRecords
        (fun j => (iterData p t M zeroWord minusOne c j v).coefficients.get) (n+1)).flatten := by
  induction n generalizing v with
  | zero =>
    simp only [generatedBits, RingTableLayout.powerRecords, List.ofFn_succ,
      List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
 iterData, vectorRecords_flat]
  | succ n ih =>
    rw [powerRecords_succ, List.flatten_append]
    change wordBits v.coefficients.val ++ (wordBits (advance p t M zeroWord minusOne c v).coefficients.val ++
      generatedBits p t M zeroWord minusOne c n (advance p t M zeroWord minusOne c v)) =
      (List.ofFn (fun i => (v.coefficients.get i).val)).flatten ++
        (RingTableLayout.powerRecords
          (fun j => (iterData p t M zeroWord minusOne c j (advance p t M zeroWord minusOne c v)).coefficients.get) (n+1)).flatten
    rw [vectorRecords_flat, ← ih]

theorem allPowerBits_eq_powerRecords (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d) (oneWord zeroWord minusOne : Word (baseWidth p t)) :
    allPowerBits p t M c oneWord zeroWord minusOne =
      (RingTableLayout.powerRecords (fun j =>
        (iterData p t M zeroWord minusOne c j (initialData d oneWord zeroWord)).coefficients.get)
        (2*d-1)).flatten := by
  have hn : (2*d-2)+1 = 2*d-1 := by omega
  simpa only [allPowerBits, hn] using
    generatedBits_eq_powerRecords p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)

open SubexponentialSAT.BinaryArithmetic in
theorem nativeTable_eq_callback (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (hd : 0 < d) (c : List.Vector (Word (baseWidth p t)) d)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t) :
    RingTriple.tableEncoding (fun i j k =>
      (iterData p t M cache.zero cache.minusOne c (i.val+j.val)
        (initialData d cache.one cache.zero)).coefficients.get k) =
      RingTriple.tableEncoding (RingProgram.structureTableRun
        (RingProgram.scalarProgram p t M cache) c.get).1 := by
  congr 1
  funext i j k
  simpa only [RingProgram.structureTableRun, List.Vector.get_ofFn] using
    powerData_eq_callback p t M cache hd c hz ho (i.val+j.val) k

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
