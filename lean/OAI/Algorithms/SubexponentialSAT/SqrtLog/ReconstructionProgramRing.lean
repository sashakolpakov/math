import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Source-preserving CRT adapters for the native arbitrary-degree ring
programs. The adapter is a fixed finite table. Its cost includes three input
copies, the actual native trace, output copying and cleanup. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

/-- Native arithmetic uses its own bank; the four retained caches are shared
with the local polynomial services. -/
def ports : Fin 32 ↪ Fin 256 := ⟨
  ![128,129,130,131,132,194,134,135,136,137,138,139,202,141,142,143,
    144,203,146,147,148,149,201,151,152,153,154,155,156,157,158,159], by decide⟩

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective 8 8⟩

def nativeStacks (modulus width zero table result x y degree : List Bool) :
    Fin 32 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (fun _ => [])
      0 result) 5 modulus) 8 x) 9 y) 11 degree) 12 width) 17 zero) 22 table

def initialNative (base : Store) (x y : List Bool) : Fin 32 → List Bool :=
  nativeStacks (base 194) (base 202) (base 203) (base 201) [] x y (base 204)

def finalNative (base : Store) (out : List Bool) : Fin 32 → List Bool :=
  nativeStacks (base 194) (base 202) (base 203) (base 201) out [] [] []

def Ready (base : Store) : Prop :=
  base 120 = [] ∧ ∀ i, base (ports i) = finalNative base [] i

abbrev nativeCall {l : ℕ} (p : Program 8 32 l) : Code :=
  .call (ProgramLinking.liftProgram p registers ports)

abbrev command {l : ℕ} (p : Program 8 32 l) : Code :=
  .seq (copy 240 136) (.seq (copy 241 137) (.seq (copy 204 139)
    (.seq (nativeCall p) (.seq (copy 128 244) (clear 128)))))

def callResult (s : Store) (out : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    136 []) 137 []) 139 []) 128 out

/-- This contract refers to the actual native program trace. -/
abbrev NativeSpec {C : Type*} {l : ℕ} (base : Store) (encode : C → List Bool)
    (p : Program 8 32 l) (op : C → C → C) (K : ℕ) : Prop :=
  ∀ (regs : Fin 8 → Bool) (a b : C), ∃ rf,
    RunsIn p K
      ((⟨regs, initialNative base (encode a) (encode b)⟩ : State 8 32).withPC (some p.entry))
      ((⟨rf, finalNative base (encode (op a b))⟩ : State 8 32).withPC none)

theorem nativeCall_run {C : Type*} {l : ℕ}
    (base : Store) (encode : C → List Bool) (p : Program 8 32 l)
    (op : C → C → C) (K : ℕ) (hnative : NativeSpec base encode p op K)
    (s : Store) (a b : C)
    (hinput : ∀ i, s (ports i) = initialNative base (encode a) (encode b) i) :
    ExecutesIn (nativeCall p) K s (callResult s (encode (op a b))) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  let localIn := projectState registers ports d
  obtain ⟨rf, n, hn, ht⟩ := hnative localIn.regs a b
  have hi : localIn.stacks = initialNative base (encode a) (encode b) := funext hinput
  let localOut : State 8 32 := ⟨rf, finalNative base (encode (op a b))⟩
  have trace : Trace p n (localIn.withPC (some p.entry)) (localOut.withPC none) := by
    simpa only [localOut, ← hi] using ht
  have hr := eval_call_from_state p registers ports d registers.injective ports.injective trace
  have hout : localOut.stacks = Function.update (Function.update
      (Function.update (Function.update localIn.stacks 8 []) 9 []) 11 []) 0 (encode (op a b)) := by
    rw [hi]
    funext i
    fin_cases i <;> simp [localOut, finalNative, initialNative, nativeStacks]
  have hbase : Function.extend ports localIn.stacks d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers ports d registers.injective ports.injective)
  have hs : (embedState registers ports d localOut).stacks = callResult s (encode (op a b)) := by
    change Function.extend ports localOut.stacks d.stacks = _
    rw [hout, ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hbase]
    rfl
  have he : embedState registers ports d localOut =
      (⟨(embedState registers ports d localOut).regs, callResult s (encode (op a b))⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hs
  rw [he] at hr
  exact ⟨n, _, hn, hr⟩

theorem ports_low (i : Fin 32) : (ports i).val < 205 := by
  fin_cases i <;> decide

theorem command_spec {C : Type*} {l : ℕ}
    (base : Store) (encode : C → List Bool) (p : Program 8 32 l)
    (op : C → C → C) (K W : ℕ) (hready : Ready base)
    (hnative : NativeSpec base encode p op K) (hw : ∀ a, (encode a).length ≤ W) :
    ServiceSpec base encode (command p) op (K + 23 * W + 7 * (base 204).length + 23) := by
  intro s a b hf ha hb ho ht
  have hs (i : Fin 32) : s (ports i) = finalNative base [] i :=
    (hf (ports i) (ports_low i)).trans (hready.2 i)
  have h120 : s 120 = [] := (hf 120 (by decide)).trans hready.1
  have h128 : s 128 = [] := by simpa [ports, finalNative, nativeStacks] using hs 0
  have h136 : s 136 = [] := by simpa [ports, finalNative, nativeStacks] using hs 8
  have h137 : s 137 = [] := by simpa [ports, finalNative, nativeStacks] using hs 9
  have h139 : s 139 = [] := by simpa [ports, finalNative, nativeStacks] using hs 11
  have h204 : s 204 = base 204 := hf 204 (by decide)
  let s1 := Function.update s 136 (encode a)
  let s2 := Function.update s1 137 (encode b)
  let s3 := Function.update s2 139 (base 204)
  let s4 := Function.update s 128 (encode (op a b))
  let s5 := Function.update s4 244 (encode (op a b))
  have h1 : ExecutesIn (copy 240 136) (7 * (encode a).length + 5) s s1 := by
    simpa only [ha, h136, List.append_nil, s1] using
      copy_run 240 136 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy 241 137) (7 * (encode b).length + 5) s1 s2 := by
    have h := copy_run 241 137 s1 (by decide) (by decide) (by decide)
      (by simp [s1, h120])
    simpa [s1, s2, hb, h137] using h
  have h3 : ExecutesIn (copy 204 139) (7 * (base 204).length + 5) s2 s3 := by
    have h := copy_run 204 139 s2 (by decide) (by decide) (by decide)
      (by simp [s2, s1, h120])
    simpa [s3, s2, s1, h204, h139] using h
  have hin : ∀ i, s3 (ports i) = initialNative base (encode a) (encode b) i := by
    intro i
    have h := hs i
    fin_cases i <;> simp_all [s3, s2, s1, ports, initialNative, finalNative, nativeStacks]
  have he : callResult s3 (encode (op a b)) = s4 := by
    funext i
    by_cases h1 : i = 136 <;> by_cases h2 : i = 137 <;>
      by_cases h3 : i = 139 <;> by_cases h4 : i = 128 <;>
      simp [callResult, s3, s2, s1, s4, h1, h2, h3, h4,
        h136, h137, h139]
  have h4 : ExecutesIn (nativeCall p) K s3 s4 := by
    simpa only [he] using nativeCall_run base encode p op K hnative s3 a b hin
  have h5 : ExecutesIn (copy 128 244) (7 * (encode (op a b)).length + 5) s4 s5 := by
    have h := copy_run 128 244 s4 (by decide) (by decide) (by decide)
      (by simp [s4, h120])
    simpa [s5, s4, ho] using h
  have h6 : ExecutesIn (clear 128) (2 * (encode (op a b)).length + 3) s5
      (Function.update s 244 (encode (op a b))) := by
    have h := clear_run 128 s5
    have he : Function.update s5 128 [] = Function.update s 244 (encode (op a b)) := by
      funext i
      by_cases h1 : i = 128 <;> by_cases h2 : i = 244 <;>
        simp [s5, s4, h1, h2, h128]
    rw [he] at h
    simpa [s5, s4] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  apply h.mono
  have hwa := hw a
  have hwb := hw b
  have hwc := hw (op a b)
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.RingAdapter

end OAI.Algorithms
