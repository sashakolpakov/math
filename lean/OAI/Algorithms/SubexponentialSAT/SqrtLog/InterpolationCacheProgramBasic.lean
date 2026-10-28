import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramNativeInverse
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed local cache-producer instructions and framed native service calls.
The lower256 ports are the existing arithmetic ABI; controller streams and
copy scratch occupy disjoint higher ports. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives StackRoutines

abbrev Store := Fin 320 → List Bool
abbrev Data := State 16 320
abbrev Code := Cmd 16 320

def Runs (c : Code) (K : ℕ) (s out : Store) : Prop :=
  ∀ r : Fin 16 → Bool, ∃ n rf, n ≤ K ∧ Eval c n (⟨r,s⟩ : Data) ⟨rf,out⟩

theorem Runs.mono {c : Code} {K L : ℕ} {s out : Store} (h : Runs c K s out)
    (hKL : K ≤ L) : Runs c L s out := by
  intro r
  obtain ⟨n,rf,hn,he⟩ := h r
  exact ⟨n,rf,hn.trans hKL,he⟩

theorem Runs.seq {c e : Code} {K L : ℕ} {s mid out : Store}
    (hc : Runs c K s mid) (he : Runs e L mid out) : Runs (.seq c e) (K+L) s out := by
  intro r
  obtain ⟨n,rm,hn,en⟩ := hc r
  obtain ⟨m,rf,hm,em⟩ := he rm
  exact ⟨n+m,rf,Nat.add_le_add hn hm,en.seq em⟩

def copy (src dst : Fin 320) : Code := .call (copyProgram src dst 270 0 1)
def clear (src : Fin 320) : Code := .call (clearProgram src 0 1)
def emit (src dst : Fin 320) : Code := .call (transferProgram src dst 0 1)
def reverse (src : Fin 320) : Code := .call (reverseProgram src 270 271 0 1)
def take (src dst : Fin 320) : Code := takeWord 104 270 271 src dst 0 1
def peek (src : Fin 320) : Code := .base (.atom (.peek src 0 15))

theorem copy_run (s : Store) (src dst : Fin 320) (hsd : src≠dst)
    (hs : src≠270) (hd : (270 : Fin 320)≠dst) (ht : s 270=[]) :
    Runs (copy src dst) (7*(s src).length+5) s (Function.update s dst (s src++s dst)) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,copy_eval (⟨r,s⟩ : Data) src dst 270 0 1 hsd hs hd (by decide) ht⟩

theorem clear_run (s : Store) (src : Fin 320) :
    Runs (clear src) (2*(s src).length+3) s (Function.update s src []) := by
  intro r
  refine ⟨_,readRegs r 0 1 none,le_rfl,Eval.call _ ?_⟩
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 16) 1 r s) 2 rfl rfl
  simpa [clearResult,clearProgram,clearStacks,StructuredProgram.State.withPC,Nat.add_assoc] using h

theorem emit_run (s : Store) (src dst : Fin 320) (hne : src≠dst) :
    Runs (emit src dst) (3*(s src).length+3) s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst)) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,transfer_eval (⟨r,s⟩ : Data) src dst 0 1 hne (by decide)⟩

theorem reverse_run (s : Store) (src : Fin 320) (h270 : src≠270) (h271 : src≠271)
    (ht270 : s 270=[]) (ht271 : s 271=[]) :
    Runs (reverse src) (9*(s src).length+7) s (Function.update s src (s src).reverse) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,reverse_eval (⟨r,s⟩ : Data) src 270 271 0 1
    h270 h271 (by decide) (by decide) ht270 ht271⟩

theorem take_run (s : Store) (src dst : Fin 320)
    (distinct : Function.Injective (![104,270,271,src,dst] : Fin 5 → Fin 320))
    (bits rest : List Bool) (hsrc : s src=bits++rest) (hw : (s 104).length=bits.length)
    (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (take src dst) (14*bits.length+11) s
      (Function.update (Function.update s src rest) dst (bits++s dst)) := by
  intro r
  exact ⟨_,readRegs r 0 1 none,le_rfl,takeWord_eval (⟨r,s⟩ : Data)
    104 270 271 src dst 0 1 distinct (by decide) bits rest hsrc h270 h271 hw⟩

def low (i : Fin 256) : Fin 320 := i.castAdd 64

theorem low_injective : Function.Injective low := Fin.castAdd_injective _ _

abbrev lowCall (cmd : Cmd 16 256) : Code :=
  .call (ProgramLinking.liftProgram (compiled cmd 0 0) id low)

/-- The service is a real compiled finite subprogram. Its one changed low
port is installed back into the larger controller store; all higher streams
and every other low port are preserved. -/
theorem lowCall_run (cmd : Cmd 16 256) (K : ℕ) (s : Store) (i : Fin 256) (out : List Bool)
    (h : SubexpConvolutionControl.ExecutesIn cmd K (s ∘ low) (Function.update (s ∘ low) i out)) :
    Runs (lowCall cmd) (K+1) s (Function.update s (low i) out) := by
  intro r
  obtain ⟨n,rf,hn,he⟩ := h r
  let a : Data := ⟨r,s⟩
  let b : State 16 256 := ⟨rf,Function.update (s ∘ low) i out⟩
  have hc := eval_call_from_state (compiled cmd 0 0) id low a Function.injective_id
    low_injective (compiled_halt_trace he 0 0)
  have hbase : Function.extend low (s ∘ low) s=s := by
    exact congrArg StructuredProgram.State.stacks
      (embedState_project id low a Function.injective_id low_injective)
  have hs : (embedState id low a b).stacks=Function.update s (low i) out := by
    change Function.extend low (Function.update (s ∘ low) i out) s = _
    rw [ProgramLinking.extend_update low_injective,hbase]
  have hb : embedState id low a b=
      (⟨(embedState id low a b).regs,Function.update s (low i) out⟩ : Data) :=
    state_ext rfl hs
  change Eval (lowCall cmd) (n+1) a (embedState id low a b) at hc
  rw [hb] at hc
  exact ⟨n+1,_,Nat.add_le_add_right hn 1,hc⟩

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
