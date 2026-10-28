import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramRing
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceAdd
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanService

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (ServiceSpec)

/-- Persistent native arithmetic metadata and a clean private workspace. -/
structure NativeReady (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store) : Prop where
  workspace : ReconstructionProgram.RingAdapter.Ready base
  modulus : base 194 = M.bits
  width : (base 202).length = baseWidth p t
  zero : base 203 = cache.zero.val
  table : base 201 = RingTriple.tableEncoding table
  degree : (base 204).length = d

/-- Updating the caller's two polynomial caches does not affect scalar service
readiness; all remaining low ports are retained. -/
theorem NativeReady.frame_except_low_caches {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {table : Fin d → Fin d → Fin d → Word (baseWidth p t)}
    {base s : Store} (h : NativeReady p t M cache table base)
    (hf : ∀ i : Fin 256, i.val < 205 → i ≠ 192 → i ≠ 193 → s i = base i) :
    NativeReady p t M cache table s := by
  have h194 := hf 194 (by decide) (by decide) (by decide)
  have h201 := hf 201 (by decide) (by decide) (by decide)
  have h202 := hf 202 (by decide) (by decide) (by decide)
  have h203 := hf 203 (by decide) (by decide) (by decide)
  have h204 := hf 204 (by decide) (by decide) (by decide)
  refine ⟨?_, h194.trans h.modulus, ?_, h203.trans h.zero, h201.trans h.table, ?_⟩
  · refine ⟨(hf 120 (by decide) (by decide) (by decide)).trans h.workspace.1, ?_⟩
    intro i
    have h192 : ReconstructionProgram.RingAdapter.ports i ≠ 192 := by
      fin_cases i <;> decide
    have h193 : ReconstructionProgram.RingAdapter.ports i ≠ 193 := by
      fin_cases i <;> decide
    rw [hf _ (ReconstructionProgram.RingAdapter.ports_low i) h192 h193]
    simpa only [ReconstructionProgram.RingAdapter.finalNative, h194, h201, h202, h203]
      using h.workspace.2 i
  · simpa only [h202] using h.width
  · simpa only [h204] using h.degree

/-- Readiness transports across the standard persistent low-frame relation. -/
theorem NativeReady.frame {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {table : Fin d → Fin d → Fin d → Word (baseWidth p t)}
    {base s : Store} (h : NativeReady p t M cache table base)
    (hf : CRTLocalProgram.LowFrame base s) : NativeReady p t M cache table s :=
  h.frame_except_low_caches fun i hi _ _ => hf i hi

/-- The prepared polynomial zero and unary length caches are caller-owned. -/
theorem NativeReady.update_polynomial_caches {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {table : Fin d → Fin d → Fin d → Word (baseWidth p t)}
    {base : Store} (h : NativeReady p t M cache table base) (zero count : List Bool) :
    NativeReady p t M cache table
      (Function.update (Function.update base 192 zero) 193 count) := by
  apply h.frame_except_low_caches
  intro i hi h192 h193
  simp [h192, h193]

def add : Code := ReconstructionProgram.RingAdapter.command RingScan.serviceAddProgram
def multiply : Code := ReconstructionProgram.RingAdapter.command RingScan.serviceMulProgram

def addBudget (B d : ℕ) : ℕ := RingScan.serviceAddBudget B d + 23 * (d * B) + 7*d + 24
def mulBudget (B d : ℕ) : ℕ := RingScan.serviceMulBudget B d + 23 * (d * B) + 7*d + 24

theorem nativeStacks_eq (modulus width zero table result x y degree : List Bool) :
    ReconstructionProgram.RingAdapter.nativeStacks modulus width zero table result x y degree =
      RingScan.serviceTapes ⟨modulus, result, x, y, degree, width, zero, table, [], [], [], [], []⟩ := by
  funext i
  fin_cases i <;> rfl

theorem add_native_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ReconstructionProgram.RingAdapter.NativeSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceAddProgram
      (fun x y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
      (RingScan.serviceAddBudget (baseWidth p t) d + 1) := by
  intro regs x y
  obtain ⟨rf, hr⟩ := RingScan.serviceAddProgram_run p t M cache x y regs
    (base 204) (base 202) (base 201) h.degree h.width
  refine ⟨rf, ?_⟩
  simpa only [ReconstructionProgram.RingAdapter.initialNative, ReconstructionProgram.RingAdapter.finalNative, nativeStacks_eq, h.modulus, h.zero,
    RingScan.serviceState, RingScan.serviceWorkState] using hr

theorem multiply_native_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ReconstructionProgram.RingAdapter.NativeSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceMulProgram
      (fun x y => (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
      (RingScan.serviceMulBudget (baseWidth p t) d + 1) := by
  intro regs x y
  obtain ⟨rf, hr⟩ := RingScan.serviceMulProgram_run p t M cache hz table x y regs
    (base 204) (base 202) h.degree h.width
  refine ⟨rf, ?_⟩
  simpa only [ReconstructionProgram.RingAdapter.initialNative, ReconstructionProgram.RingAdapter.finalNative, nativeStacks_eq, h.modulus, h.zero, h.table,
    RingScan.serviceState, RingScan.serviceWorkState] using hr

theorem add_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ServiceSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) add
      (fun x y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
      (addBudget (baseWidth p t) d) := by
  have hs := ReconstructionProgram.RingAdapter.command_spec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceAddProgram
    (fun x y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
    (RingScan.serviceAddBudget (baseWidth p t) d + 1) (d * baseWidth p t) h.workspace
    (add_native_spec p t M cache table base h) (fun a => (RingProgram.flat_length a).le)
  convert hs using 1 <;> simp only [add, addBudget, h.degree] ; omega

theorem multiply_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ServiceSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) multiply
      (fun x y => (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
      (mulBudget (baseWidth p t) d) := by
  have hs := ReconstructionProgram.RingAdapter.command_spec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceMulProgram
    (fun x y => (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
    (RingScan.serviceMulBudget (baseWidth p t) d + 1) (d * baseWidth p t) h.workspace
    (multiply_native_spec p t M cache hz table base h) (fun a => (RingProgram.flat_length a).le)
  convert hs using 1 <;> simp only [multiply, mulBudget, h.degree] ; omega

theorem addBudget_polynomial (B d : ℕ) :
    addBudget B d ≤ 50000 * (d+1)^3 * (B+1)^2 := by
  unfold addBudget RingScan.serviceAddBudget
  ring_nf
  omega

theorem mulBudget_polynomial (B d : ℕ) :
    mulBudget B d ≤ 50000 * (d+1)^3 * (B+1)^2 := by
  have h := RingScan.serviceMulBudget_le B d
  unfold mulBudget
  ring_nf at *
  omega

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
