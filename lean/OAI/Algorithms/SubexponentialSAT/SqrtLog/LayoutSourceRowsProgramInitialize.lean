import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructorSemantics

namespace OAI.Algorithms

/-! Fixed, width-generic initialization for the source-row executor. All
zero-array construction and copies are paid; only four output stacks change. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram

def command : Code :=
  .seq (copy 210 243)
    (.seq (SubexpPolynomialConstructor.construct 104 104 242)
      (.seq (copy 242 192) (copy 210 193)))

def budget (D W : ℕ) : ℕ := 240 * (D+1) * (W+1)

def finish (s : Store) (D W : ℕ) : Store :=
  Function.update
    (Function.update
      (Function.update (Function.update s 243 (List.replicate D true))
        242 (List.replicate (D*W) false))
      192 (List.replicate (D*W) false))
    193 (List.replicate D true)

structure Ready (s : Store) (D W : ℕ) : Prop where
  dimension : s 210 = List.replicate D true
  zeroCell : s 104 = List.replicate W false
  empty100 : s 100 = []
  empty101 : s 101 = []
  empty102 : s 102 = []
  empty107 : s 107 = []
  empty108 : s 108 = []
  empty120 : s 120 = []
  empty192 : s 192 = []
  empty193 : s 193 = []
  empty242 : s 242 = []
  empty243 : s 243 = []
  empty245 : s 245 = []

theorem padded_zero (D W : ℕ) :
    Constructor.Counter.paddedBits W (List.replicate W false)
      (List.replicate W false) D = List.replicate (D*W) false := by
  cases D with
  | zero => simp [Constructor.Counter.paddedBits]
  | succ D =>
      cases D with
      | zero => simp [Constructor.Counter.paddedBits]
      | succ D =>
          simp only [Constructor.Counter.paddedBits, ← List.replicate_add]
          congr 1
          ring

theorem command_run (s : Store) (D W : ℕ) (h : Ready s D W) :
    ExecutesIn command (budget D W) s (finish s D W) := by
  let s1 := Function.update s 243 (List.replicate D true)
  let s2 := Function.update s1 242 (List.replicate (D*W) false)
  let s3 := Function.update s2 192 (List.replicate (D*W) false)
  have h1 : ExecutesIn (copy 210 243) (7*D+5) s s1 := by
    simpa [s1, h.dimension, h.empty243] using
      copy_run 210 243 s (by decide) (by decide) (by decide) h.empty120
  have h2 : ExecutesIn (SubexpPolynomialConstructor.construct 104 104 242)
      (220*(D+1)*(W+1)) s1 s2 := by
    have hh := Constructor.construct_run s1 104 104 242
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) D W
      (by simp [s1, h.zeroCell]) (by simp [s1, h.zeroCell])
      (by simp [s1]) (by simp [s1, h.zeroCell])
      (by simp [s1, h.empty100]) (by simp [s1, h.empty101])
      (by simp [s1, h.empty102]) (by simp [s1, h.empty107])
      (by simp [s1, h.empty108]) (by simp [s1, h.empty120])
      (by simp [s1, h.empty245]) (by simp [s1, h.empty242])
    simpa only [s1, Function.update_of_ne (by decide : (104 : Fin 256) ≠ 243),
      h.zeroCell, padded_zero] using hh
  have h3 : ExecutesIn (copy 242 192) (7*(D*W)+5) s2 s3 := by
    simpa [s3, s2, s1, h.empty192] using
      copy_run 242 192 s2 (by decide) (by decide) (by decide)
        (by simp [s2, s1, h.empty120])
  have h4 : ExecutesIn (copy 210 193) (7*D+5) s3 (finish s D W) := by
    simpa [finish, s3, s2, s1, h.dimension, h.empty193] using
      copy_run 210 193 s3 (by decide) (by decide) (by decide)
        (by simp [s3, s2, s1, h.empty120])
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by unfold budget; ring_nf; omega)

theorem finish_frame (s : Store) (D W : ℕ) (i : Fin 256)
    (h243 : i ≠ 243) (h242 : i ≠ 242) (h192 : i ≠ 192) (h193 : i ≠ 193) :
    finish s D W i = s i := by
  simp [finish, h243, h242, h192, h193]

theorem encode_zero_array {B d : ℕ} (zero : Coeff B d)
    (hz : RingProgram.flat zero = List.replicate (d*B) false) (D : ℕ) :
    encode (List.replicate D zero) = List.replicate (D*(d*B)) false := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.replicate_succ, encode_cons, hz, ih, ← List.replicate_add]
      congr 1
      ring

theorem command_run_encoded {B d : ℕ} (zero : Coeff B d)
    (hz : RingProgram.flat zero = List.replicate (d*B) false)
    (s : Store) (D : ℕ) (h : Ready s D (d*B)) :
    ExecutesIn command (budget D (d*B)) s
      (Function.update
        (Function.update
          (Function.update (Function.update s 243 (List.replicate D true))
            242 (encode (List.replicate D zero)))
          192 (encode (List.replicate D zero)))
        193 (List.replicate D true)) := by
  simpa only [encode_zero_array zero hz D, finish] using command_run s D (d*B) h

def machine := compiled command 210 192

theorem machine_run (s : Store) (D W : ℕ) (h : Ready s D W)
    (regs : Fin 16 → Bool) :
    ∃ rf : Fin 16 → Bool,
      RunsIn machine (budget D W+1)
        ((⟨regs,s⟩ : Data).withPC (some machine.entry))
        ((⟨rf,finish s D W⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_run s D W h regs
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 210 192⟩

theorem machine_primitive (s : Store) (D W : ℕ) (h : Ready s D W)
    (regs : Fin 16 → Bool) :
    ∃ rf : Fin 16 → Bool,
      Computation.RunsIn (primitive machine).step
        (primitiveOverhead machine * (budget D W+1))
        (primitiveCfg machine ((⟨regs,s⟩ : Data).withPC (some machine.entry)))
        (primitiveCfg machine ((⟨rf,finish s D W⟩ : Data).withPC none)) := by
  obtain ⟨rf,he⟩ := machine_run s D W h regs
  exact ⟨rf,BitProgram.primitive_execution machine he⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize

end OAI.Algorithms
