import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramPass
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramFrame

namespace OAI.Algorithms

/-! Native scans for inverse nodes, negative nodes, and a complete row of
pairwise difference inverses. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

theorem Ready.update_controller {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {minusOne : Coeff t d} {s : Store} (h : Ready t a M cache minusOne s)
    (i : Fin 320) (v : List Bool) (hi : i∈controllerPorts) :
    Ready t a M cache minusOne (Function.update s i v) :=
  h.frame ((Frame.refl s).update i v hi)

def inverseScan : Code := scanMaster 257 259 213 inverseCommand
def negativeScan : Code := scanMaster 257 260 213 negativeCommand
def rowScan : Code := scanMaster 258 261 218 inverseCommand

def nodeScanBudget (K W Q : ℕ) := Q*(K+26*W+19)+7

theorem inverseScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hready : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=[]) (harg : s 213=[]) (hresult : s 208=[])
    (hother : s 218=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1) :
    Runs inverseScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s
      (Function.update s 259 ((xs.flatMap fun x => RingProgram.flat (inverseValue t a M cache minusOne x)).reverse++s 259)) := by
  apply scanMaster_run RingProgram.flat (inverseValue t a M cache minusOne) _ _ hW
    RingProgram.flat_length 257 259 213 (by unfold MapPorts; decide) (by decide) inverseCommand
    (fun s => Ready t a M cache minusOne s ∧ s 218=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    ?_ ?_ s xs ⟨hready,hother⟩ hm hsrc harg hresult hready.width
    (hready.scratch 270 (by decide)) (hready.scratch 271 (by decide))
  · intro s i v h hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact ⟨h.1.update_controller _ v (by decide),by simpa using h.2⟩
  · intro s x h hx hr
    exact h.1.inverse_run hz x _ hx h.2 hr

theorem negativeScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hready : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 257=[]) (harg : s 213=[]) (hresult : s 208=[]) :
    Runs negativeScan (nodeScanBudget (negativeBudget t d) (d*baseWidth 3 t) xs.length) s
      (Function.update s 260 ((xs.flatMap fun x => RingProgram.flat (negativeValue t a M cache minusOne x)).reverse++s 260)) := by
  apply scanMaster_run RingProgram.flat (negativeValue t a M cache minusOne) _ _ hW
    RingProgram.flat_length 257 260 213 (by unfold MapPorts; decide) (by decide) negativeCommand
    (Ready t a M cache minusOne) ?_ ?_ s xs hready hm hsrc harg hresult hready.width
    (hready.scratch 270 (by decide)) (hready.scratch 271 (by decide))
  · intro s i v h hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact h.update_controller _ v (by decide)
  · intro s x h hx hr
    exact h.negative_run hz x hx hr

theorem rowScan_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t) (minusOne x : Coeff t d)
    (hW : 0 < d*baseWidth 3 t) (s : Store) (xs : List (Coeff t d))
    (hready : Ready t a M cache minusOne s) (hm : s 256=xs.flatMap RingProgram.flat)
    (hsrc : s 258=[]) (harg : s 218=[]) (hresult : s 208=[])
    (htheta : s 213=RingProgram.flat x) :
    Runs rowScan (nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) xs.length) s
      (Function.update s 261 ((xs.flatMap fun y => RingProgram.flat (differenceValue t a M cache minusOne x y)).reverse++s 261)) := by
  apply scanMaster_run RingProgram.flat (differenceValue t a M cache minusOne x) _ _ hW
    RingProgram.flat_length 258 261 218 (by unfold MapPorts; decide) (by decide) inverseCommand
    (fun s => Ready t a M cache minusOne s ∧ s 213=RingProgram.flat x)
    ?_ ?_ s xs ⟨hready,htheta⟩ hm hsrc harg hresult hready.width
    (hready.scratch 270 (by decide)) (hready.scratch 271 (by decide))
  · intro s i v h hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact ⟨h.1.update_controller _ v (by decide),by simpa using h.2⟩
  · intro s y h hy hr
    exact h.1.inverse_run hz x y h.2 hy hr

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
