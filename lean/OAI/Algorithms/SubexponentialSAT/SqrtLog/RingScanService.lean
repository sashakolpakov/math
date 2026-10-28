import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceLifts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceAdd
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleBounds

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev serviceDegree : Cmd 8 32 := serviceTransfer 11 15

theorem serviceDegree_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval serviceDegree (3*s.degree.length+3)
      (serviceWorkState regs {s with outer := []})
      (serviceWorkState (readRegs regs 1 3 none) {s with degree := [], outer := s.degree.reverse}) := by
  have he := serviceTransfer_eval (serviceWorkState regs {s with outer := []}) 11 15 (by decide)
  convert he using 1
  · simp [serviceWorkState, serviceTapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [ serviceWorkState, serviceTapes, transferStacks]

abbrev serviceFinish : Cmd 8 32 := serviceClear 16

theorem serviceFinish_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval serviceFinish (2*s.inner.length+3)
      (serviceWorkState regs s)
      (serviceWorkState (readRegs regs 1 3 none) {s with inner := []}) := by
  have he := serviceClear_eval (serviceWorkState regs s) 16
  convert he using 1
  · simp [serviceWorkState, serviceTapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [ serviceWorkState, serviceTapes, clearStacks]

abbrev serviceMul : Cmd 8 32 := .seq servicePrepare (.seq serviceExpand
  (.seq serviceRoute (.seq serviceCount (.seq serviceDegree (.seq serviceContract serviceFinish)))))

def serviceMulBudget (B d : ℕ) : ℕ :=
  (7*(d^3*B)+5) + (RingTriple.expandBudget B d+1) +
  (4*d*B+18*B*d^3+12) + (7*d^2+14*d+8) + (3*d+3) +
  (d*(d*d*(18000*(B+1)^2+48*B+51)+13*B+18)+6) + (2*d^2+3)

private theorem tripleBits_length {B : ℕ} (triples : List (WordTriple B)) :
    (tripleBits triples).length = triples.length * (3*B) := by
  induction triples with
  | nil => simp [tripleBits]
  | cons x xs ih =>
      have h1 : x.1.val.length = B := x.1.property
      have h2 : x.2.1.val.length = B := x.2.1.property
      have h3 : x.2.2.val.length = B := x.2.2.property
      simp [tripleBits, ih, h1, h2, h3]
      ring

private theorem blockBits_length_uniform {B m : ℕ} (blocks : List (List (WordTriple B)))
    (hm : ∀ b ∈ blocks, b.length = m) :
    (blockBits blocks).length = blocks.length * (m*(3*B)) := by
  induction blocks with
  | nil => simp [blockBits]
  | cons b bs ih =>
      have hb := hm b (by simp)
      have hs := ih (fun b hb => hm b (by simp [hb]))
      simp only [blockBits, List.length_append, tripleBits_length, hb, hs, List.length_cons]
      ring

private theorem multiplicationBits_length {B d : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d) :
    (blockBits (multiplicationBlocks table x y)).length = 3*B*d^3 := by
  rw [blockBits_length_uniform _ (multiplicationBlocks_uniform table x y), multiplicationBlocks_length]
  ring

theorem serviceMulBudget_le (B d : ℕ) :
    serviceMulBudget B d ≤ 40000*(d+1)^3*(B+1)^2 := by
  unfold serviceMulBudget RingTriple.expandBudget
  ring_nf
  omega

/-- Complete native multiplication, including table copying, paid triple
expansion, both unary counters, scalar contraction, and all cleanup. The
cached table is preserved; its one-time construction is a separate service. -/
theorem serviceMul_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ serviceMulBudget (baseWidth p t) d, ∃ rf, Eval serviceMul n
      (serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width
        cache.zero.val (RingTriple.tableEncoding table))
      (serviceState rf M.bits
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
        [] [] [] width cache.zero.val (RingTriple.tableEncoding table)) := by
  let initial : ServiceStore := ⟨M.bits, [], RingProgram.flat x, RingProgram.flat y,
    degree, width, cache.zero.val, RingTriple.tableEncoding table, [], [], [], [], []⟩
  let expanded : ServiceStore := {initial with stream := blockBits (multiplicationBlocks table x y)}
  let routed : ServiceStore := {initial with x := [], y := expanded.stream}
  let counted : ServiceStore := {routed with inner := repeatCount degree degree.length}
  let output : ServiceStore := ⟨M.bits,
    RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1,
    [], [], [], width, cache.zero.val, RingTriple.tableEncoding table, [], counted.inner, [], [], []⟩
  have h1 := servicePrepare_eval regs initial
  obtain ⟨n, hn, r1, h2⟩ := serviceExpand_eval table x y (readRegs regs 1 3 none)
    M.bits [] degree width cache.zero.val [] [] hd hw
  have h3 := serviceRoute_eval r1 expanded
  obtain ⟨r2, h4⟩ := serviceCount_eval (readRegs r1 1 3 none) routed
  have h5 := serviceDegree_eval r2 counted
  have hinner : counted.inner.length = d*d := by simp [counted, hd]
  obtain ⟨m, hm, r3, h6⟩ := serviceContract_eval p t M cache hz table x y
    (readRegs r2 1 3 none) width degree.reverse counted.inner (by simpa using hd) hinner hw
  have h7 := serviceFinish_eval r3 output
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  refine ⟨_, ?_, readRegs r3 1 3 none, he⟩
  simp only [initial, expanded, routed, counted, output, hd, RingProgram.flat_length,
    repeatCount_length]
  unfold serviceMulBudget
  rw [RingTriple.tableEncoding_length, multiplicationBits_length]
  nlinarith

abbrev serviceMulProgram : Program 8 32 (size serviceMul+1) := compiled serviceMul 8 0

theorem serviceMulProgram_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn serviceMulProgram (serviceMulBudget (baseWidth p t) d+1)
      ((serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width
        cache.zero.val (RingTriple.tableEncoding table)).withPC (some serviceMulProgram.entry))
      ((serviceState rf M.bits
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
        [] [] [] width cache.zero.val (RingTriple.tableEncoding table)).withPC none) := by
  obtain ⟨n, hn, rf, ht⟩ := serviceMul_eval p t M cache hz table x y regs degree width hd hw
  exact ⟨rf, n+1, Nat.add_le_add_right hn 1, compiled_halt_trace ht 8 0⟩


/-- The fixed service compiles to a primitive bit machine; the constant
simulation overhead depends only on the instruction table. -/
theorem serviceMul_primitive (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ rf, Computation.RunsIn (primitive serviceMulProgram).step
      (primitiveOverhead serviceMulProgram * (40000*(d+1)^3*(baseWidth p t+1)^2+1))
      (primitiveCfg serviceMulProgram
        ((serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width
          cache.zero.val (RingTriple.tableEncoding table)).withPC (some serviceMulProgram.entry)))
      (primitiveCfg serviceMulProgram
        ((serviceState rf M.bits
          (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
          [] [] [] width cache.zero.val (RingTriple.tableEncoding table)).withPC none)) := by
  obtain ⟨rf, hr⟩ := serviceMulProgram_run p t M cache hz table x y regs degree width hd hw
  refine ⟨rf, ?_⟩
  exact (BitProgram.primitive_execution _ hr).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (serviceMulBudget_le (baseWidth p t) d) 1))

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
