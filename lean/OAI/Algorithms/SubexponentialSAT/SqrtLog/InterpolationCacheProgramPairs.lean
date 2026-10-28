import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramRows

namespace OAI.Algorithms

/-! Nested native scans producing the full row-major difference-inverse
array. Every diagonal cell is computed by the same total inverse routine. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open SubexpLiftRing
private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def pairStep : Code := take 257 213 ;; rowScan ;; clear 213
def pairLoop : Code := .while 15 (pairStep ;; peek 257)
def pairScan : Code := copy 256 257 ;; peek 257 ;; pairLoop

def rowBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) (x : Coeff t d) : List Bool :=
  xs.flatMap fun y => RingProgram.flat (differenceValue t a M cache minusOne x y)

theorem pairStep_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne x : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d)) (rest : List Bool)
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=RingProgram.flat x++rest)
    (hclean : ∀i∈([208,213,218,258] : List (Fin 320)),s i=[]) :
    Runs pairStep (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+16*(d*baseWidth 3 t)+14) s
      (Function.update (Function.update s 257 rest) 261 ((rowBytes t a M cache minusOne xs x).reverse++s 261)) := by
  let s1 := Function.update (Function.update s 257 rest) 213 (RingProgram.flat x)
  let s2 := Function.update s1 261 ((rowBytes t a M cache minusOne xs x).reverse++s 261)
  have h1 : Runs (take 257 213) (14*(d*baseWidth 3 t)+11) s s1 := by
    simpa only [s1,hclean 213 (by simp),List.append_nil,RingProgram.flat_length] using
      take_run s 257 213 (by decide) (RingProgram.flat x) rest hsrc
        (hr.width.trans (RingProgram.flat_length x).symm)
        (hr.scratch 270 (by decide)) (hr.scratch 271 (by decide))
  have hr1 : Ready t a M cache minusOne s1 :=
    (hr.update_controller 257 rest (by decide)).update_controller 213 _ (by decide)
  have h2 : Runs rowScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s1 s2 := by
    have hs1 : s1 261 = s 261 := by simp [s1]
    simpa only [s2, rowBytes, hs1] using
      rowScan_run t a M cache hz minusOne x hW s1 xs hr1
        (by simpa [s1] using hm) (by simpa [s1] using hclean 258 (by simp))
        (by simpa [s1] using hclean 218 (by simp))
        (by simpa [s1] using hclean 208 (by simp)) (by simp [s1])
  have h3 : Runs (clear 213) (2*(d*baseWidth 3 t)+3) s2 (Function.update s2 213 []) := by
    simpa [s2,s1,RingProgram.flat_length] using clear_run s2 213
  have he : Function.update s2 213 []=
      Function.update (Function.update s 257 rest) 261 ((rowBytes t a M cache minusOne xs x).reverse++s 261) := by
    funext i
    by_cases hi : i=213
    · subst i; simp [s2,s1,hclean 213 (by simp)]
    · simp [s2,s1,Function.update_apply,hi]
  rw [he] at h3
  exact (h1.seq (h2.seq h3)).mono (by omega)

theorem pairLoop_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (xs ys : List (Coeff t d))
    (s : Store) (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=ys.flatMap RingProgram.flat)
    (hclean : ∀i∈([208,213,218,258] : List (Fin 320)),s i=[])
    (r : Fin 16 → Bool) :
    ∃n rf,n ≤ ys.length*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length+16*(d*baseWidth 3 t)+16)+1 ∧
      Eval pairLoop n (⟨readRegs r 0 15 (s 257).head?,s⟩ : Data)
        ⟨rf,Function.update (Function.update s 257 []) 261
          ((ys.flatMap (rowBytes t a M cache minusOne xs)).reverse++s 261)⟩ := by
  induction ys generalizing s r with
  | nil =>
      have hs : s 257=[] := hsrc
      have hu : Function.update s 257 []=s := by simpa only [hs] using Function.update_eq_self 257 s
      refine ⟨1,readRegs r 0 15 none,by simp,?_⟩
      simp only [List.flatMap_nil,List.reverse_nil,List.nil_append,hu,Function.update_eq_self]
      simpa only [pairLoop, hs,List.head?_nil] using
        (Eval.while_false (body := pairStep ;; peek 257)
          (a := (⟨readRegs r 0 15 none,s⟩ : Data)) (by simp [readRegs]))
  | cons x ys ih =>
      let mid := Function.update (Function.update s 257 (ys.flatMap RingProgram.flat)) 261
        ((rowBytes t a M cache minusOne xs x).reverse++s 261)
      obtain ⟨n,rm,hn,he⟩ := pairStep_run t a M cache hz minusOne x hW s xs
        (ys.flatMap RingProgram.flat) hr hm hsrc hclean (readRegs r 0 15 (s 257).head?)
      have hrm : Ready t a M cache minusOne mid :=
        (hr.update_controller 257 _ (by decide)).update_controller 261 _ (by decide)
      obtain ⟨m,rf,hmb,het⟩ := ih mid hrm (by simpa [mid] using hm) (by simp [mid])
        (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl|rfl|rfl|rfl <;> simpa [mid] using hclean _ (by simp)) rm
      have hg : (readRegs r 0 15 (s 257).head?) 15=true := by
        have hne : RingProgram.flat x≠[] := by
          intro hh
          have h := RingProgram.flat_length x
          rw [hh,List.length_nil] at h
          omega
        rw [hsrc,List.flatMap_cons]
        cases hh : RingProgram.flat x with
        | nil => exact (hne hh).elim
        | cons b bs => simp [readRegs]
      have hc := Eval.while_true hg (he.seq (peek_eval mid rm 257)) het
      refine ⟨n+1+m+1,rf,?_,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
      · have hfinal : Function.update (Function.update mid 257 []) 261
            ((ys.flatMap (rowBytes t a M cache minusOne xs)).reverse++mid 261) =
            Function.update (Function.update s 257 []) 261
              (((x::ys).flatMap (rowBytes t a M cache minusOne xs)).reverse++s 261) := by
          funext i
          by_cases hi : i=261
          · subst i; simp [mid,List.reverse_append,List.append_assoc]
          · by_cases hj : i=257
            · subst i; simp [mid]
            · simp [mid,hi,hj]
        rw [hfinal] at hc
        exact hc

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
