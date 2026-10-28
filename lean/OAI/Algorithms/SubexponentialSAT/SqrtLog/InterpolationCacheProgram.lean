import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramTables
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramCounts

namespace OAI.Algorithms

/-! A single fixed native interpolation-cache producer. The only data
inputs are the actual node stream and already prepared ring constants.
No inverse, negative, or pairwise table is supplied to this program. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing
private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def command : Code := inverseTable ;; negativeTable ;; differenceTable ;;
  countCopy 256 262 ;; countCopy 104 263

def program := compiled command 256 261

def inputEmpty : List (Fin 320) := [208,213,218,257,258,259,260,261,262,263,272]

def finalStore (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update s
    259 (inverseBytes t a M cache minusOne xs))
    260 (negativeBytes t a M cache minusOne xs))
    261 (differenceBytes t a M cache minusOne xs))
    262 (List.replicate (xs.length*(d*baseWidth 3 t)) true))
    263 (List.replicate (d*baseWidth 3 t) true)

def budget (t d Q : ℕ) := inverseTableBudget t d Q + negativeTableBudget t d Q +
  differenceTableBudget t d Q + 11*(Q*(d*baseWidth 3 t))+9+11*(d*baseWidth 3 t)+9

theorem command_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈inputEmpty,s i=[]) :
    Runs command (budget t d xs.length) s (finalStore t a M cache minusOne xs s) := by
  let s1 := Function.update s 259 (inverseBytes t a M cache minusOne xs)
  let s2 := Function.update s1 260 (negativeBytes t a M cache minusOne xs)
  let s3 := Function.update s2 261 (differenceBytes t a M cache minusOne xs)
  let s4 := Function.update s3 262 (List.replicate (xs.length*(d*baseWidth 3 t)) true)
  have h1 : Runs inverseTable (inverseTableBudget t d xs.length) s s1 :=
    inverseTable_run t a M cache hz minusOne hW s xs hr hm (by
      intro i hi
      apply hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide)
  have hr1 := hr.update_controller 259 (inverseBytes t a M cache minusOne xs) (by decide)
  have h2 : Runs negativeTable (negativeTableBudget t d xs.length) s1 s2 :=
    negativeTable_run t a M cache hz minusOne hW s1 xs hr1 (by simpa [s1] using hm) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> simpa [s1] using hc _ (by decide))
  have hr2 := hr1.update_controller 260 (negativeBytes t a M cache minusOne xs) (by decide)
  have h3 : Runs differenceTable (differenceTableBudget t d xs.length) s2 s3 :=
    differenceTable_run t a M cache hz minusOne hW s2 xs hr2 (by simpa [s2,s1] using hm) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> simpa [s2,s1] using hc _ (by decide))
  have hlen : (s3 256).length=xs.length*(d*baseWidth 3 t) := by
    simp only [s3,s2,s1,Function.update_of_ne (by decide : (256:Fin 320)≠259),
      Function.update_of_ne (by decide : (256:Fin 320)≠260),
      Function.update_of_ne (by decide : (256:Fin 320)≠261),hm]
    exact flatMap_length _ _ RingProgram.flat_length xs
  have h4 : Runs (countCopy 256 262) (11*(xs.length*(d*baseWidth 3 t))+9) s3 s4 := by
    simpa only [hlen,s4] using countCopy_run 256 262 s3 (by decide) (by decide) (by decide)
      (by simpa [s3,s2,s1] using hr.scratch 270 (by decide))
      (by simpa [s3,s2,s1] using hc 272 (by decide))
      (by simpa [s3,s2,s1] using hc 262 (by decide))
  have h5 : Runs (countCopy 104 263) (11*(d*baseWidth 3 t)+9) s4
      (finalStore t a M cache minusOne xs s) := by
    have hwidth : (s4 104).length=d*baseWidth 3 t := by simpa [s4,s3,s2,s1] using hr.width
    simpa only [hwidth,finalStore,s4,s3,s2,s1] using
      countCopy_run 104 263 s4 (by decide) (by decide) (by decide)
        (by simpa [s4,s3,s2,s1] using hr.scratch 270 (by decide))
        (by simpa [s4,s3,s2,s1] using hc 272 (by decide))
        (by simpa [s4,s3,s2,s1] using hc 263 (by decide))
  exact (h1.seq (h2.seq (h3.seq (h4.seq h5)))).mono (by unfold budget; omega)

theorem finalStore_frame (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) (s : Store) (i : Fin 320)
    (hi : i∉([259,260,261,262,263] : List (Fin 320))) :
    finalStore t a M cache minusOne xs s i=s i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp only [finalStore,Function.update_of_ne hi.1,Function.update_of_ne hi.2.1,
    Function.update_of_ne hi.2.2.1,Function.update_of_ne hi.2.2.2.1,
    Function.update_of_ne hi.2.2.2.2]

theorem program_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hr : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hc : ∀i∈inputEmpty,s i=[]) (r : Fin 16 → Bool) :
    ∃n rf,n ≤ budget t d xs.length+1 ∧ Trace program n
      ((⟨r,s⟩ : Data).withPC (some program.entry))
      ((⟨rf,finalStore t a M cache minusOne xs s⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_run t a M cache hz minusOne hW s xs hr hm hc r
  exact ⟨n+1,rf,Nat.add_le_add_right hn 1,compiled_halt_trace he 256 261⟩

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
