import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramMachine
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramSerialization

namespace OAI.Algorithms

/-! Concrete native Newton lift and the exact degree-three coefficient output.
The input-state contract includes prepared scalar constants and the cached
H-adic table; native preparation is a separate remaining construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

local instance ternaryPrimeFinal : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev newtonProgram : Program 8 41 (size newtonMachine+1) := compiled newtonMachine 32 32

def nativeLiftBudget (t counterWidth : ℕ) : ℕ :=
  7*Nat.clog 2 t*arithmeticBudget (baseWidth 3 t) (3*t) +
    (Nat.clog 2 t+1)*(16*counterWidth+16)+1

def binaryLiftWords (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t) :
    RingProgram.Code (RingProgram.ScalarCode 3 t) (3*t) :=
  (liftRun (binaryArrayProgram (RingProgram.scalarProgram 3 t M cache) t)
    (initialRun (RingProgram.scalarProgram 3 t M cache) t u).1 t).1

/-- An actual fixed finite bit program computes every Newton iteration and all
array arithmetic from the supplied prepared state. -/
theorem nativeLiftWords_run (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (u : RingProgram.ScalarCode 3 t)
    (degree width : List Bool) (hd : degree.length = 3*t) (hw : width.length = baseWidth 3 t)
    (regs : Registers (RingProgram.Code (RingProgram.ScalarCode 3 t) (3*t)))
    (state : RegisterData)
    (encoded : RegistersEncoded M.bits width cache.zero.val
      (RingTriple.tableEncoding (tableCode (t:=t) (RingProgram.scalarProgram 3 t M cache))) degree
      (minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1 regs state)
    (hinitial : regs 0 = (initialRun (RingProgram.scalarProgram 3 t M cache) t u).1)
    (hcounter : CounterPrograms.value (state.stacks 39) = Nat.clog 2 t)
    (hs : state.stacks 40 = []) :
    ∃ next : RegisterData, RunsIn newtonProgram (nativeLiftBudget t (state.stacks 39).length)
      (state.withPC (some newtonProgram.entry)) (next.withPC none) ∧
      next.stacks 32 = RingProgram.flat (binaryLiftWords t M cache u) := by
  obtain ⟨n,next,he,henc,hn⟩ := newtonMachine_exact 3 t M cache hz
    (tableCode (t:=t) (RingProgram.scalarProgram 3 t M cache))
    (zeroCode (RingProgram.scalarProgram 3 t M cache) t)
    (oneCode (RingProgram.scalarProgram 3 t M cache) t)
    (minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1
    degree width hd hw regs state encoded hs
  refine ⟨next, ⟨n+1, ?_, compiled_halt_trace he 32 32⟩, ?_⟩
  · simpa only [nativeLiftBudget, hcounter] using Nat.add_le_add_right hn 1
  · have ho := henc.values 0
    rw [liftCode_result, hcounter, hinitial] at ho
    exact ho

variable {R K : Type*} [CommRing R] [CommRing K]

/-- The words computed by the native lift have exactly the required indicator
semantics. Degree below three is structural via `digitPolynomial_degree`. -/
theorem binaryLiftWords_indicator [DecidableEq K]
    (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (hu : 2*wordValue 3 t u = 1)
    (φ : ZMod (3^t) →+* R) (ρ : R →+* K)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    (∑ s : Fin t,
      (digitPolynomial (RingProgram.scalarRing 3 t M cache)
        (binaryLiftWords t M cache u) s).eval₂ φ x * hValue x^s.val) =
      if ρ x = 0 then 1 else 0 := by
  simp only [digitPolynomial_eval]
  rw [← evaluate_digits]
  exact binaryArrayLift_indicator (RingProgram.scalarRing 3 t M cache) φ ρ t u hu q hq hker x hx

end SubexponentialSAT.SqrtLog.IdempotentProgram


end OAI.Algorithms
