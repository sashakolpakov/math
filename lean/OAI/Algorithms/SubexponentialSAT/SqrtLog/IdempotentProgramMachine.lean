import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramService
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramBinary
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanService

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- This instruction dispatcher is fixed, independent of every ring parameter. -/
def arithmeticService : ArithmeticInstruction → Cmd 8 41
  | .add dst x y => registerBinary (callService RingScan.serviceAdd)
      (arrayRegister dst) (arrayRegister x) (arrayRegister y)
  | .mul dst x y => registerBinary (callService RingScan.serviceMul)
      (arrayRegister dst) (arrayRegister x) (arrayRegister y)
  | .neg dst x => registerBinary (callService RingScan.serviceMul)
      (arrayRegister dst) 36 (arrayRegister x)

def newtonPorts : CounterForPrograms.Ports 8 41 where
  register := ⟨Fin.castAdd 5, by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
  counter := 39
  scratch := 40
  counter_ne_scratch := by decide

abbrev newtonMachine : Cmd 8 41 := nativeNewtonLoop newtonPorts arithmeticService

structure RegistersEncoded {B d : ℕ} (modulus width zero table degree : List Bool)
    (minusOne : RingProgram.Code (Word B) d)
    (regs : Registers (RingProgram.Code (Word B) d)) (state : RegisterData) : Prop where
  context : ServiceContext state modulus width zero table
  values : ∀ i, state.stacks (arrayRegister i) = RingProgram.flat (regs i)
  negativeUnit : state.stacks 36 = RingProgram.flat minusOne
  degree : state.stacks 37 = degree
  copyScratch : state.stacks 38 = []

theorem arrayRegister_injective : Function.Injective arrayRegister := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [arrayRegister] at hv
  omega

theorem RegistersEncoded.update {B d : ℕ} {modulus width zero table degree : List Bool}
    {minusOne : RingProgram.Code (Word B) d}
    {regs : Registers (RingProgram.Code (Word B) d)} {state next : RegisterData}
    (h : RegistersEncoded modulus width zero table degree minusOne regs state)
    (dst : Fin 4) (value : RingProgram.Code (Word B) d)
    (hs : next.stacks = Function.update state.stacks (arrayRegister dst) (RingProgram.flat value)) :
    RegistersEncoded modulus width zero table degree minusOne (Function.update regs dst value) next := by
  constructor
  · intro i
    have hi : servicePorts i ≠ arrayRegister dst := by
      intro he
      have hv := congrArg Fin.val he
      have := i.isLt
      dsimp [servicePorts, arrayRegister] at hv
      omega
    rw [hs, Function.update_of_ne hi]
    exact h.context i
  · intro i
    rw [hs]
    by_cases hi : i = dst
    · subst i; simp
    · simp [Function.update_of_ne hi, arrayRegister_injective.ne hi, h.values]
  · have hi : (36 : Fin 41) ≠ arrayRegister dst := by
      intro he; have hv := congrArg Fin.val he; have := dst.isLt
      dsimp [arrayRegister] at hv; omega
    rw [hs, Function.update_of_ne hi]
    exact h.negativeUnit
  · have hi : (37 : Fin 41) ≠ arrayRegister dst := by
      intro he; have hv := congrArg Fin.val he; have := dst.isLt
      dsimp [arrayRegister] at hv; omega
    rw [hs, Function.update_of_ne hi]
    exact h.degree
  · have hi : (38 : Fin 41) ≠ arrayRegister dst := by
      intro he; have hv := congrArg Fin.val he; have := dst.isLt
      dsimp [arrayRegister] at hv; omega
    rw [hs, Function.update_of_ne hi]
    exact h.copyScratch

theorem RegistersEncoded.frame {B d : ℕ} {modulus width zero table degree : List Bool}
    {minusOne : RingProgram.Code (Word B) d}
    {regs : Registers (RingProgram.Code (Word B) d)} {state next : RegisterData}
    (hf : CounterForPrograms.OutsideEq newtonPorts state next)
    (h : RegistersEncoded modulus width zero table degree minusOne regs state) :
    RegistersEncoded modulus width zero table degree minusOne regs next := by
  constructor
  · intro i
    have hi39 : servicePorts i ≠ newtonPorts.counter := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [servicePorts, newtonPorts] at hv; omega
    have hi40 : servicePorts i ≠ newtonPorts.scratch := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [servicePorts, newtonPorts] at hv; omega
    rw [← hf _ hi39 hi40]
    exact h.context i
  · intro i
    have hi39 : arrayRegister i ≠ newtonPorts.counter := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [arrayRegister, newtonPorts] at hv; omega
    have hi40 : arrayRegister i ≠ newtonPorts.scratch := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [arrayRegister, newtonPorts] at hv; omega
    rw [← hf _ hi39 hi40]
    exact h.values i
  · rw [← hf 36 (by decide) (by decide)]
    exact h.negativeUnit
  · rw [← hf 37 (by decide) (by decide)]
    exact h.degree
  · rw [← hf 38 (by decide) (by decide)]
    exact h.copyScratch

/-- All scans, scalar operations, register copies, and call halts are included. -/
def arithmeticBudget (B d : ℕ) : ℕ :=
  max (RingScan.serviceAddBudget B d) (RingScan.serviceMulBudget B d) +
    25*(d*B) + 7*d + 27

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- One fully measured register update, ready to instantiate with either
native arithmetic service. All source ports may coincide with the target. -/
theorem registerArrayStep {B dim : ℕ} (command : Cmd 8 32)
    (modulus width zero table degree : List Bool) (hd : degree.length = dim)
    (minusOne : RingProgram.Code (Word B) dim)
    (regs : Registers (RingProgram.Code (Word B) dim)) (state : RegisterData)
    (encoded : RegistersEncoded modulus width zero table degree minusOne regs state)
    (target : Fin 4) (left right : Fin 41)
    (x y value : RingProgram.Code (Word B) dim)
    (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : state.stacks left = RingProgram.flat x)
    (hy : state.stacks right = RingProgram.flat y)
    (bound : ℕ)
    (hbound : bound ≤ max (RingScan.serviceAddBudget B dim) (RingScan.serviceMulBudget B dim))
    (run : ∀ flags : Fin 8 → Bool,
      ∃ n ≤ bound, ∃ rf, Eval command n
        (RingScan.serviceState flags modulus [] (RingProgram.flat x) (RingProgram.flat y)
          degree width zero table)
        (RingScan.serviceState rf modulus (RingProgram.flat value) [] [] [] width zero table)) :
    ∃ n next, n ≤ arithmeticBudget B dim ∧
      Eval (registerBinary (callService command) (arrayRegister target) left right) n state next ∧
      RegistersEncoded modulus width zero table degree minusOne
        (Function.update regs target value) next ∧
      next.stacks 39 = state.stacks 39 ∧ next.stacks 40 = state.stacks 40 := by
  obtain ⟨n, hn, rf, hrun⟩ := run (preparedOperands state left right).regs
  have ht : 32 ≤ (arrayRegister target).val := by dsimp [arrayRegister]; omega
  have ht38 : arrayRegister target ≠ 38 := by
    intro h; have hv := congrArg Fin.val h; have := target.isLt
    dsimp [arrayRegister] at hv; omega
  obtain ⟨next, hnext, hstacks⟩ := registerService_eval command state modulus width zero table degree
    (RingProgram.flat x) (RingProgram.flat y) (RingProgram.flat value)
    (arrayRegister target) left right n rf encoded.context encoded.degree hx hy encoded.copyScratch
    ht hl hr ht38 hl38 hr38 hrun
  refine ⟨_, next, ?_, hnext, encoded.update target value hstacks, ?_, ?_⟩
  · rw [encoded.values target, RingProgram.flat_length, RingProgram.flat_length,
      RingProgram.flat_length, RingProgram.flat_length, hd]
    unfold arithmeticBudget
    omega
  · rw [hstacks]
    have h39 : (39 : Fin 41) ≠ arrayRegister target := by
      intro h; have hv := congrArg Fin.val h; have := target.isLt
      dsimp [arrayRegister] at hv; omega
    exact Function.update_of_ne h39 _ _
  · rw [hstacks]
    have h40 : (40 : Fin 41) ≠ arrayRegister target := by
      intro h; have hv := congrArg Fin.val h; have := target.isLt
      dsimp [arrayRegister] at hv; omega
    exact Function.update_of_ne h40 _ _

theorem arithmeticService_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {dim : ℕ} (table : Fin dim → Fin dim → Fin dim → Word (baseWidth p t))
    (zero one minusOne : RingProgram.Code (Word (baseWidth p t)) dim)
    (degree width : List Bool) (hd : degree.length = dim) (hw : width.length = baseWidth p t) :
    NativeInstructionSpec
      (binaryProgram (RingProgram.program (RingProgram.scalarProgram p t M cache) table zero one) minusOne)
      newtonPorts arithmeticService
      (RegistersEncoded M.bits width cache.zero.val (RingTriple.tableEncoding table) degree minusOne)
      (arithmeticBudget (baseWidth p t) dim) := by
  intro instruction regs state encoded hscratch
  have port_low (i : Fin 4) : 32 ≤ (arrayRegister i).val := by dsimp [arrayRegister]; omega
  have port_tmp (i : Fin 4) : arrayRegister i ≠ 38 := by
    intro h; have hv := congrArg Fin.val h; have := i.isLt
    dsimp [arrayRegister] at hv; omega
  cases instruction with
  | add dst x y =>
      obtain ⟨n,next,hn,he,henc,hcounter,hs⟩ := registerArrayStep
        RingScan.serviceAdd M.bits width cache.zero.val (RingTriple.tableEncoding table)
        degree hd minusOne regs state encoded dst (arrayRegister x) (arrayRegister y)
        (regs x) (regs y) (RingProgram.addRun (RingProgram.scalarProgram p t M cache) (regs x) (regs y)).1
        (port_low x) (port_low y) (port_tmp x) (port_tmp y) (encoded.values x) (encoded.values y)
        (RingScan.serviceAddBudget (baseWidth p t) dim) (le_max_left _ _)
        (fun flags => RingScan.serviceAdd_eval p t M cache (regs x) (regs y) flags degree width
          (RingTriple.tableEncoding table) hd hw)
      exact ⟨n,next,hn,he,henc,hcounter,hs.trans hscratch⟩
  | mul dst x y =>
      obtain ⟨n,next,hn,he,henc,hcounter,hs⟩ := registerArrayStep
        RingScan.serviceMul M.bits width cache.zero.val (RingTriple.tableEncoding table)
        degree hd minusOne regs state encoded dst (arrayRegister x) (arrayRegister y)
        (regs x) (regs y) (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table (regs x) (regs y)).1
        (port_low x) (port_low y) (port_tmp x) (port_tmp y) (encoded.values x) (encoded.values y)
        (RingScan.serviceMulBudget (baseWidth p t) dim) (le_max_right _ _)
        (fun flags => RingScan.serviceMul_eval p t M cache hz table (regs x) (regs y) flags degree width hd hw)
      exact ⟨n,next,hn,he,henc,hcounter,hs.trans hscratch⟩
  | neg dst x =>
      obtain ⟨n,next,hn,he,henc,hcounter,hs⟩ := registerArrayStep
        RingScan.serviceMul M.bits width cache.zero.val (RingTriple.tableEncoding table)
        degree hd minusOne regs state encoded dst 36 (arrayRegister x)
        minusOne (regs x) (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table minusOne (regs x)).1
        (by decide) (port_low x) (by decide) (port_tmp x) encoded.negativeUnit (encoded.values x)
        (RingScan.serviceMulBudget (baseWidth p t) dim) (le_max_right _ _)
        (fun flags => RingScan.serviceMul_eval p t M cache hz table minusOne (regs x) flags degree width hd hw)
      exact ⟨n,next,hn,he,henc,hcounter,hs.trans hscratch⟩

/-- No native arithmetic hypothesis remains in this theorem. The input carries
its cached table, constants, dimension/width data, and starting arrays. -/
theorem newtonMachine_exact (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {dim : ℕ} (table : Fin dim → Fin dim → Fin dim → Word (baseWidth p t))
    (zero one minusOne : RingProgram.Code (Word (baseWidth p t)) dim)
    (degree width : List Bool) (hd : degree.length = dim) (hw : width.length = baseWidth p t)
    (regs : Registers (RingProgram.Code (Word (baseWidth p t)) dim)) (state : RegisterData)
    (encoded : RegistersEncoded M.bits width cache.zero.val (RingTriple.tableEncoding table) degree minusOne regs state)
    (hs : state.stacks 40 = []) :
    ∃ n next, Eval newtonMachine n state next ∧
      RegistersEncoded M.bits width cache.zero.val (RingTriple.tableEncoding table) degree minusOne
        (codeRun
          (binaryProgram (RingProgram.program (RingProgram.scalarProgram p t M cache) table zero one) minusOne)
          (liftCode (CounterPrograms.value (state.stacks 39))) regs).1 next ∧
      n ≤ 7*CounterPrograms.value (state.stacks 39)*arithmeticBudget (baseWidth p t) dim +
        (CounterPrograms.value (state.stacks 39)+1)*(16*(state.stacks 39).length+16) := by
  exact nativeNewtonLoop_exact _ newtonPorts arithmeticService _ _
    (arithmeticService_spec p t M cache hz table zero one minusOne degree width hd hw)
    (fun _ _ _ hf hh => RegistersEncoded.frame hf hh) regs state encoded hs

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

/-- A fixed polynomial bound for one complete register operation. -/
theorem arithmeticBudget_polynomial (B d : ℕ) :
    arithmeticBudget B d ≤ 41000*(d+1)^3*(B+1)^2 := by
  have hm := RingScan.serviceMulBudget_le B d
  have ha : RingScan.serviceAddBudget B d ≤ 40000*(d+1)^3*(B+1)^2 := by
    unfold RingScan.serviceAddBudget
    ring_nf
    omega
  have hx := max_le ha hm
  unfold arithmeticBudget
  calc
    _ ≤ 40000*(d+1)^3*(B+1)^2 + 25*(d*B) + 7*d + 27 := by omega
    _ ≤ _ := by ring_nf; omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
