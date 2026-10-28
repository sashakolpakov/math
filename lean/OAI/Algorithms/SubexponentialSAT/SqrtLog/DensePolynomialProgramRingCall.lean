import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanService
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramPorts
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A framed native extension-ring multiplication for the dense convolution
controller. Its live operands are 198/199, result200, persistent degree204.
The private 32-stack ring workspace is separated from the array controller. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod


def native : Code := .call (ProgramLinking.liftProgram RingScan.serviceMulProgram registers ports)
def command : Code := .seq (copy 204 139) native

def budget (B d : ℕ) : ℕ := 7*d+5 + (RingScan.serviceMulBudget B d+1)

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t)

theorem native_run (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (s : Store) (degree width : List Bool) (hd : degree.length = d)
    (hw : width.length = baseWidth p t)
    (hs : ∀ i, s (ports i) = (RingScan.serviceState (fun _ => false) M.bits []
      (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val
      (RingTriple.tableEncoding table)).stacks i) :
    ExecutesIn native (RingScan.serviceMulBudget (baseWidth p t) d+1) s
      (Function.update (Function.update (Function.update (Function.update s 198 []) 199 [])
        139 []) 200 (RingProgram.flat
          (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)) := by
  intro regs
  let start := RingScan.serviceState (regs ∘ registers) M.bits []
    (RingProgram.flat x) (RingProgram.flat y) degree width cache.zero.val
    (RingTriple.tableEncoding table)
  obtain ⟨rf,n,hn,ht⟩ := RingScan.serviceMulProgram_run p t M cache hz table x y
    (regs ∘ registers) degree width hd hw
  have hp : projectState registers ports (⟨regs,s⟩ : Data) = start := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; exact hs i
  have hc := eval_call_from_state RingScan.serviceMulProgram registers ports
    (⟨regs,s⟩ : Data) registers.injective ports.injective (by simpa only [hp] using ht)
  let output := RingProgram.flat
    (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1
  have hout : (RingScan.serviceState rf M.bits output [] [] [] width cache.zero.val
      (RingTriple.tableEncoding table)).stacks =
      Function.update (Function.update (Function.update (Function.update start.stacks
        8 []) 9 []) 11 []) 0 output := by
    funext i
    fin_cases i <;> simp [start, RingScan.serviceState, RingScan.serviceWorkState, RingScan.serviceTapes]
  have hi : Function.extend ports start.stacks s = s := extend_agree ports start.stacks s hs
  have he : embedState registers ports (⟨regs,s⟩ : Data)
      (RingScan.serviceState rf M.bits output [] [] [] width cache.zero.val
        (RingTriple.tableEncoding table)) =
      (⟨Function.extend registers rf regs,
        Function.update (Function.update (Function.update (Function.update s 198 []) 199 [])
          139 []) 200 output⟩ : Data) := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · change Function.extend ports _ s = _
      rw [hout, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, hi]
      rfl
  change Eval native n (⟨regs,s⟩ : Data)
    (embedState registers ports (⟨regs,s⟩ : Data)
      (RingScan.serviceState rf M.bits output [] [] [] width cache.zero.val
        (RingTriple.tableEncoding table))) at hc
  rw [he] at hc
  exact ⟨n, Function.extend registers rf regs, hn, hc⟩

theorem command_run (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (s : Store) (width : List Bool) (hd : (s 204).length = d)
    (hw : width.length = baseWidth p t) (h120 : s 120 = [])
    (hs : ∀ i, s (ports i) = (RingScan.serviceState (fun _ => false) M.bits []
      (RingProgram.flat x) (RingProgram.flat y) [] width cache.zero.val
      (RingTriple.tableEncoding table)).stacks i) :
    ExecutesIn command (budget (baseWidth p t) d) s
      (Function.update (Function.update (Function.update s 198 []) 199 []) 200
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)) := by
  have h139 : s 139 = [] := hs 11
  let next := Function.update s 139 (s 204)
  have h1 : ExecutesIn (copy 204 139) (7*d+5) s next := by
    simpa [next,hd,h139] using copy_run 204 139 s (by decide) (by decide) (by decide) h120
  have hnext : ∀ i, next (ports i) = (RingScan.serviceState (fun _ => false) M.bits []
      (RingProgram.flat x) (RingProgram.flat y) (s 204) width cache.zero.val
      (RingTriple.tableEncoding table)).stacks i := by
    intro i
    have hi := hs i
    fin_cases i <;> simp [next,ports,port,RingScan.serviceState,
      RingScan.serviceWorkState,RingScan.serviceTapes] at hi ⊢ <;> exact hi
  have h2 := native_run p t M cache hz table x y next (s 204) width hd hw hnext
  have he : Function.update (Function.update (Function.update (Function.update next 198 []) 199 [])
      139 []) 200 (RingProgram.flat
          (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1) =
      Function.update (Function.update (Function.update s 198 []) 199 []) 200
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1) := by
    funext i
    by_cases hi : i = 139 <;> simp [next,Function.update_apply,hi,h139]
  rw [he] at h2
  exact h1.seq h2

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.RingCall

end OAI.Algorithms
