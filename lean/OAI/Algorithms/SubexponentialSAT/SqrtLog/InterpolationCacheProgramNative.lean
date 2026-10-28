import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramModel

namespace OAI.Algorithms

/-! Actual finite arithmetic subprograms used in the cache scans. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing

def inverseCommand : Code := lowCall CRTLocalProgram.NativeInverse.command

def negativeCommand : Code := lowCall
  (CRTLocalProgram.callAt HornerProgram.Services.multiply 213 211 208)

def inverseBudget (t d : ℕ) := CRTLocalProgram.NativeInverse.budget t d + 1

def negativeBudget (t d : ℕ) :=
  HornerProgram.Services.mulBudget (baseWidth 3 t) d + 40*(d*baseWidth 3 t)+51

theorem inverseCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (s : Store)
    (hr : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) (s ∘ low))
    (x y minusOne : Coeff t d)
    (hx : s 213=RingProgram.flat x) (hy : s 218=RingProgram.flat y)
    (hzero : s 104=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hm : s 211=RingProgram.flat minusOne)
    (hq : (s 209).length=3^d-2) (ht : (s 212).length=t)
    (hc : ∀i∈CRTLocalProgram.NativeInverse.work, s (low i)=[]) :
    Runs inverseCommand (inverseBudget t d) s
      (Function.update s 208 (RingProgram.flat (differenceValue t a M cache minusOne x y))) := by
  exact lowCall_run _ _ s 208 _ (CRTLocalProgram.NativeInverse.command_run
    t a M cache hz (s ∘ low) hr x y minusOne hx hy hzero hone hm hq ht hc)

theorem negativeCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (s : Store)
    (hr : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) (s ∘ low))
    (x minusOne : Coeff t d) (hx : s 213=RingProgram.flat x) (hm : s 211=RingProgram.flat minusOne)
    (hc : ∀i∈([208,240,241,244,245] : List (Fin 320)), s i=[]) :
    Runs negativeCommand (negativeBudget t d) s
      (Function.update s 208 (RingProgram.flat (negativeValue t a M cache minusOne x))) := by
  have h := CRTLocalProgram.callAt_run (s ∘ low) RingProgram.flat
    HornerProgram.Services.multiply
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d) (d*baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (HornerProgram.modelTable t a M cache) (s ∘ low) hr)
    (fun x => (RingProgram.flat_length x).le) (s ∘ low) x minusOne 213 211 208
    (by decide) (by decide) (by decide) (CRTLocalProgram.lowFrame_refl _) hx hm
    hr.workspace.1 (hc 240 (by simp)) (hc 241 (by simp)) (hc 244 (by simp)) (hc 245 (by simp))
    (by change (s 208).length ≤ d*baseWidth 3 t; rw [hc 208 (by simp)]; exact Nat.zero_le _)
  exact lowCall_run _ _ s 208 _ h

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
