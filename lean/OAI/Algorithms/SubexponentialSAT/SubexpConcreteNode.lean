import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeRealization
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyExecution

namespace OAI.Algorithms

/-!
# The concrete sparsification node in the protected main layout

The code below instantiates the port compiler with the implemented node
program. Its execution theorem has data-invariant premises only; it does not
assume the correctness of a supplied splitter implementation.
-/

namespace SubexponentialSAT.SubexpConcreteNode

open BitProgram StructuredCalls SubexpMainProgram SubexpNodePorts

abbrev Frame (c : SubexpSetupProgram.Config) (er : ℕ) :=
  State (workRegs er) (totalStacks (SubexpSetupProgram.mainExtraStacks c))

def localFrame (c : SubexpSetupProgram.Config) {er : ℕ}
    (hr : 32 ≤ workRegs er) (frame : Frame c er) : ExecSparsifyNode.Data c.k :=
  projectState (registerMap hr) (setupStackMap c) frame

def program (c : SubexpSetupProgram.Config) {er : ℕ} (hr : 32 ≤ workRegs er) :=
  liftNode (ExecSparsifyProgram.program c.k) (SubexpSetupProgram.helperSize c)
    (by have := SubexpSetupProgram.helperSize_ge c; omega) (setup_fit c).le hr

def FrameReady (c : SubexpSetupProgram.Config) {er : ℕ} (frame : Frame c er) : Prop :=
  (∀ i, frame.regs i = false) ∧
    ∀ i, 5 ≤ i.val → i.val < 37 → frame.stacks i = []

def BankValues (c : SubexpSetupProgram.Config) {er : ℕ}
    (z : ℕ → ℕ) (frame : Frame c er) : Prop :=
  ∀ i : Fin (c.k - 1), BinaryArithmetic.toNat
    (frame.stacks (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i))) =
      z (i.val + 2)

theorem local_ready (c : SubexpSetupProgram.Config) {er : ℕ}
    (hr : 32 ≤ workRegs er) (frame : Frame c er) (hf : FrameReady c frame) :
    ExecSparsifyBoundary.FrameReady (localFrame c hr frame) := by
  constructor
  · exact SubexpNodeRealization.project_regs_zero _ _ hr frame hf.1
  · intro i hlo hhi
    exact SubexpNodeRealization.project_work_empty _ _ hr frame hf.2 i hlo hhi

theorem search_threshold_eq (k : ℕ) (i : ExecCNFWidthDriver.Width k) :
    ExecSparsifyProgram.searchPort k
        (ExecCNFWidthLoad.bank k (ExecCNFWidthDriver.dimension i)
          (ExecCNFWidthDriver.dimension_le i)) = thresholdPort k i := by
  apply Fin.ext
  change 5 + (33 + (i.val + 2)) = 40 + i.val
  omega

theorem local_bank (c : SubexpSetupProgram.Config) {er : ℕ}
    (hr : 32 ≤ workRegs er) (frame : Frame c er) (z : ℕ → ℕ)
    (hb : BankValues c z frame) :
    ExecSparsifyObserved.BankValues z (localFrame c hr frame) := by
  intro i
  rw [search_threshold_eq]
  have he := SubexpNodeRealization.setup_project_threshold c hr frame i
  change (localFrame c hr frame).stacks (thresholdPort c.k i) = _ at he
  rw [he]
  exact hb i

noncomputable def branching (c : SubexpSetupProgram.Config) {er n : ℕ}
    (hr : 32 ≤ workRegs er) (frame : Frame c er) (z : ℕ → ℕ)
    (hf : FrameReady c frame) (hb : BankValues c z frame)
    (hz : ∀ d, 2 ≤ d → d ≤ c.k → 2 ≤ z d) :
    ExecSparsifyWorklist.Branching (ExecSparsifyObserved.Formula n) :=
  ExecSparsifyObserved.branching (localFrame c hr frame) z
    (local_ready c hr frame hf) (local_bank c hr frame z hb) hz

noncomputable def cost (c : SubexpSetupProgram.Config) {er n : ℕ}
    (hr : 32 ≤ workRegs er) (frame : Frame c er) (z : ℕ → ℕ)
    (hf : FrameReady c frame) (hb : BankValues c z frame)
    (hz : ∀ d, 2 ≤ d → d ≤ c.k → 2 ≤ z d) (F : ExecSparsifyObserved.Formula n) : ℕ :=
  ExecSparsifyExecution.cost (localFrame c hr frame) z
    (local_ready c hr frame hf) (local_bank c hr frame z hb) hz F

/-- The fixed, implemented node program realizes its own observed branch
in the main frame. All runtime thresholds are read from the protected bank. -/
theorem realizes (c : SubexpSetupProgram.Config) {er n : ℕ}
    (hr : 32 ≤ workRegs er) (frame : Frame c er) (z : ℕ → ℕ)
    (hf : FrameReady c frame) (hb : BankValues c z frame)
    (hz : ∀ d, 2 ≤ d → d ≤ c.k → 2 ≤ z d) :
    ExecWorklistLoop.Ambient.BoundedRealizesOn (program c hr)
      (SubexpMainSparsify.mainPorts er (SubexpSetupProgram.mainExtraStacks c)).register
      (SubexpMainSparsify.mainPorts er (SubexpSetupProgram.mainExtraStacks c)).coreStack
      frame ExecSparsifyObserved.encode (branching (n := n) c hr frame z hf hb hz).split
      (ExecSparsifyObserved.Ready c.k) (cost c hr frame z hf hb hz) := by
  apply SubexpNodeRealization.setup_realizes c (ExecSparsifyProgram.program c.k)
    hr frame ExecSparsifyObserved.encode _ (ExecSparsifyObserved.Ready c.k) _
  exact ExecSparsifyExecution.realizes (localFrame c hr frame) z
    (local_ready c hr frame hf) (local_bank c hr frame z hb) hz

theorem branching_closed (c : SubexpSetupProgram.Config) {er n : ℕ}
    (hr : 32 ≤ workRegs er) (frame : Frame c er) (z : ℕ → ℕ)
    (hf : FrameReady c frame) (hb : BankValues c z frame)
    (hz : ∀ d, 2 ≤ d → d ≤ c.k → 2 ≤ z d) :
    ExecSparsifyWorklist.SplitClosed (branching (n := n) c hr frame z hf hb hz).split
      (ExecSparsifyObserved.Ready c.k) :=
  ExecSparsifyObserved.branching_closed (localFrame c hr frame) z
    (local_ready c hr frame hf) (local_bank c hr frame z hb) hz

end SubexponentialSAT.SubexpConcreteNode

end OAI.Algorithms
