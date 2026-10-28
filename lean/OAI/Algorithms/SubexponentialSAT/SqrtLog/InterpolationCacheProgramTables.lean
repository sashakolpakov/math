import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramPairs

namespace OAI.Algorithms

/-! Complete ordered native tables; all working streams are empty again. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing
private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def inverseTable : Code := copy 104 218 ;; inverseScan ;; clear 218 ;; reverse 259
def negativeTable : Code := negativeScan ;; reverse 260
def differenceTable : Code := pairScan ;; reverse 261

def inverseBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.flatMap fun x => RingProgram.flat (inverseValue t a M cache minusOne x)

def negativeBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.flatMap fun x => RingProgram.flat (negativeValue t a M cache minusOne x)

def differenceBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.flatMap (rowBytes t a M cache minusOne xs)

def inverseTableBudget (t d Q : ℕ) :=
  nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) Q+9*(d*baseWidth 3 t)+9*(Q*(d*baseWidth 3 t))+15

def negativeTableBudget (t d Q : ℕ) :=
  nodeScanBudget (negativeBudget t d) (d*baseWidth 3 t) Q+9*(Q*(d*baseWidth 3 t))+7

def differenceTableBudget (t d Q : ℕ) :=
  Q*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) Q+23*(d*baseWidth 3 t)+16)+9*(Q*(Q*(d*baseWidth 3 t)))+14

theorem inverseTable_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,218,257,259] : List (Fin 320)),s i=[]) :
    Runs inverseTable (inverseTableBudget t d xs.length) s
      (Function.update s 259 (inverseBytes t a M cache minusOne xs)) := by
  let ni := inverseBytes t a M cache minusOne xs
  let s1 := Function.update s 218 (s 104)
  let s2 := Function.update s1 259 ni.reverse
  let s3 := Function.update s 259 ni.reverse
  have h1 : Runs (copy 104 218) (7*(d*baseWidth 3 t)+5) s s1 := by
    simpa only [s1,hc 218 (by simp),List.append_nil,hr.width] using
      copy_run s 104 218 (by decide) (by decide) (by decide) (hr.scratch 270 (by decide))
  have hr1 := hr.update_controller 218 (s 104) (by decide)
  have h2 : Runs inverseScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s1 s2 := by
    simpa [s2,s1,ni,inverseBytes,hc 259 (by simp)] using
      inverseScan_run t a M cache hz minusOne hW s1 xs hr1 (by simpa [s1] using hm)
        (by simpa [s1] using hc 257 (by simp)) (by simpa [s1] using hc 213 (by simp))
        (by simpa [s1] using hc 208 (by simp)) (by simpa [s1] using hr.zero)
  have h3 : Runs (clear 218) (2*(d*baseWidth 3 t)+3) s2 s3 := by
    have he : Function.update s2 218 []=s3 := by
      funext i
      by_cases hi : i=218 <;> simp [s3,s2,s1,Function.update_apply,hi,hc 218 (by simp)]
    simpa only [he,s2,s1,Function.update_of_ne (by decide : (218:Fin 320)≠259),
      Function.update_same,hr.width] using clear_run s2 218
  have hlen : ni.length=xs.length*(d*baseWidth 3 t) :=
    flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs
  have h4 : Runs (reverse 259) (9*(xs.length*(d*baseWidth 3 t))+7) s3
      (Function.update s 259 ni) := by
    simpa [s3,hlen] using reverse_run s3 259 (by decide) (by decide)
      (by simpa [s3] using hr.scratch 270 (by decide))
      (by simpa [s3] using hr.scratch 271 (by decide))
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by unfold inverseTableBudget; omega)

theorem negativeTable_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,257,260] : List (Fin 320)),s i=[]) :
    Runs negativeTable (negativeTableBudget t d xs.length) s
      (Function.update s 260 (negativeBytes t a M cache minusOne xs)) := by
  let nn := negativeBytes t a M cache minusOne xs
  let mid := Function.update s 260 nn.reverse
  have h1 : Runs negativeScan (nodeScanBudget (negativeBudget t d) (d*baseWidth 3 t) xs.length) s mid := by
    simpa only [mid,nn,negativeBytes,hc 260 (by simp),List.append_nil] using
      negativeScan_run t a M cache hz minusOne hW s xs hr hm (hc 257 (by simp))
        (hc 213 (by simp)) (hc 208 (by simp))
  have hlen : nn.length=xs.length*(d*baseWidth 3 t) :=
    flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs
  have h2 : Runs (reverse 260) (9*(xs.length*(d*baseWidth 3 t))+7) mid (Function.update s 260 nn) := by
    simpa [mid,hlen] using reverse_run mid 260 (by decide) (by decide)
      (by simpa [mid] using hr.scratch 270 (by decide))
      (by simpa [mid] using hr.scratch 271 (by decide))
  exact (h1.seq h2).mono (by unfold negativeTableBudget; omega)

theorem pairScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,218,257,258] : List (Fin 320)),s i=[]) :
    Runs pairScan
      (xs.length*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+23*(d*baseWidth 3 t)+16)+7) s
      (Function.update s 261 ((differenceBytes t a M cache minusOne xs).reverse++s 261)) := by
  let mid := Function.update s 257 (xs.flatMap RingProgram.flat)
  have h1 : Runs (copy 256 257) (7*(xs.length*(d*baseWidth 3 t))+5) s mid := by
    simpa only [mid,hm,hc 257 (by simp),List.append_nil,flatMap_length _ _ RingProgram.flat_length] using
      copy_run s 256 257 (by decide) (by decide) (by decide) (hr.scratch 270 (by decide))
  intro r
  obtain ⟨n,rm,hn,he⟩ := h1 r
  obtain ⟨m,rf,hmb,het⟩ := pairLoop_run t a M cache hz minusOne hW xs xs mid
    (hr.update_controller 257 _ (by decide)) (by simpa [mid] using hm) (by simp [mid])
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> simpa [mid] using hc _ (by simp)) rm
  have hend : Function.update (Function.update mid 257 []) 261
      ((xs.flatMap (rowBytes t a M cache minusOne xs)).reverse++mid 261) =
      Function.update s 261 ((differenceBytes t a M cache minusOne xs).reverse++s 261) := by
    simp [mid,differenceBytes,Function.update_idem,←hc 257 (by simp)]
  rw [hend] at het
  exact ⟨n+(1+m),rf,by nlinarith only [hn,hmb],he.seq ((peek_eval mid rm 257).seq het)⟩

theorem differenceTable_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈([208,213,218,257,258,261] : List (Fin 320)),s i=[]) :
    Runs differenceTable (differenceTableBudget t d xs.length) s
      (Function.update s 261 (differenceBytes t a M cache minusOne xs)) := by
  let nd := differenceBytes t a M cache minusOne xs
  let mid := Function.update s 261 nd.reverse
  have h1 : Runs pairScan
      (xs.length*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+23*(d*baseWidth 3 t)+16)+7) s mid := by
    simpa only [mid,nd,hc 261 (by simp),List.append_nil] using
      pairScan_run t a M cache hz minusOne hW s xs hr hm (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl <;> exact hc _ (by simp))
  have hlen : nd.length=xs.length*(xs.length*(d*baseWidth 3 t)) := by
    apply flatMap_length
    intro x
    exact flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs
  have h2 : Runs (reverse 261) (9*(xs.length*(xs.length*(d*baseWidth 3 t)))+7) mid
      (Function.update s 261 nd) := by
    simpa [mid,hlen] using reverse_run mid 261 (by decide) (by decide)
      (by simpa [mid] using hr.scratch 270 (by decide))
      (by simpa [mid] using hr.scratch 271 (by decide))
  exact (h1.seq h2).mono (by unfold differenceTableBudget; omega)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
