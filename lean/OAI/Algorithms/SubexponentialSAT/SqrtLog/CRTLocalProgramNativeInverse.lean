import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramDifference
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramModel

namespace OAI.Algorithms

/-! A standalone native inverse of a node difference. The exponent is the
residue-field cardinality minus two; the separate repair loop has length t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing

def command : Code := differenceInverseCommand
  HornerProgram.Services.multiply HornerProgram.Services.add

abbrev program : Program 16 256 (size command + 1) := compiled command 218 208

def work : List (Fin 256) := [205,208,219,220,222,240,241,244,245,246]

def value (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (theta other minusOne : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  let ops := RingProgram.modelProgram t a M cache
  let mul := fun x y => (ops.mulRun x y).1
  let add := fun x y => (ops.addRun x y).1
  inverseValue mul add ops.zeroRun.1 ops.oneRun.1 minusOne
    (differenceValue mul add theta other minusOne) (3^d-2) t

def budget (t d : ℕ) : ℕ :=
  let Km := HornerProgram.Services.mulBudget (baseWidth 3 t) d
  let Ka := HornerProgram.Services.addBudget (baseWidth 3 t) d
  inverseBudget (3^d-2) t Km Ka (d*baseWidth 3 t) + Km+Ka+102*(d*baseWidth 3 t)+113

theorem command_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store)
    (hready : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s)
    (theta other minusOne : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (htheta : s 213 = RingProgram.flat theta) (hother : s 218 = RingProgram.flat other)
    (hzero : s 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hminus : s 211 = RingProgram.flat minusOne)
    (hq : (s 209).length = 3^d-2) (ht : (s 212).length = t)
    (hclean : ∀ i ∈ work, s i = []) :
    ExecutesIn command (budget t d) s
      (Function.update s 208 (RingProgram.flat (value t a M cache theta other minusOne))) := by
  have h := differenceInverseCommand_run s RingProgram.flat
    HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d*baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (HornerProgram.modelTable t a M cache) s hready)
    (HornerProgram.Services.add_spec 3 t M cache (HornerProgram.modelTable t a M cache) s hready)
    (fun x => (RingProgram.flat_length x).le) s theta other
    (RingProgram.modelProgram t a M cache).zeroRun.1
    (RingProgram.modelProgram t a M cache).oneRun.1 minusOne (lowFrame_refl s)
    htheta hother hzero hone hminus hready.workspace.1
    (hclean 205 (by simp [work])) (hclean 208 (by simp [work]))
    (hclean 219 (by simp [work])) (hclean 220 (by simp [work]))
    (hclean 222 (by simp [work])) (hclean 240 (by simp [work]))
    (hclean 241 (by simp [work])) (hclean 244 (by simp [work]))
    (hclean 245 (by simp [work])) (hclean 246 (by simp [work]))
  simpa only [command, budget, value, hq, ht] using h

theorem program_run (s : Store) (out : List Bool) (K : ℕ)
    (h : ExecutesIn command K s (Function.update s 208 out)) (regs : Fin 16 → Bool) :
    ∃ rf, RunsIn program (K+1)
      ((⟨regs,s⟩ : Data).withPC (some program.entry))
      ((⟨rf,Function.update s 208 out⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := h regs
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 218 208⟩

theorem value_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (theta other minusOne : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hn : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hne : a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode theta) ≠
      a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode other)) :
    (RingProgram.modelRing t ht hd a M cache).decode (value t a M cache theta other minusOne) *
      ((RingProgram.modelRing t ht hd a M cache).decode theta -
        (RingProgram.modelRing t ht hd a M cache).decode other) = 1 := by
  let ops := RingProgram.modelRing t ht hd a M cache
  exact differenceInverse_correct ops.decode
    (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    ops.mul_correct ops.add_correct theta other ops.zeroRun.1 ops.oneRun.1 minusOne
    ops.zero_correct ops.one_correct hn (a.rho t ht) (3^d)
    (by simpa only [Nat.card_eq_fintype_card] using a.residue_cardinality)
    3 t (a.prime_power_zero t) (fun x hx => (a.rho_eq_zero_iff t ht x).mp hx) hne

end SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse

end OAI.Algorithms
