import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeFrame

namespace OAI.Algorithms

/-! Measured export of a native worker result followed by full worker cleanup.
The caller's high bank is retained, including arbitrary register-save tails. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram

abbrev workerCall (body : Cmd 40 768) : Cmd 40 896 :=
  liftCommand body 0 0 id workerStack
noncomputable def workerResult (a : FrameData) (b : State 40 768) : FrameData :=
  embedState id workerStack a b

theorem workerCall_eval (body : Cmd 40 768) (a : FrameData) (b : State 40 768) (n : ℕ)
    (he : Eval body n (projectState id workerStack a) b) :
    Eval (workerCall body) (n+1) a (workerResult a b) :=
  eval_liftCommand_from_state body 0 0 id workerStack a Function.injective_id
    (Fin.castAdd_injective 768 128) he

theorem workerResult_low (a : FrameData) (b : State 40 768) (i : Fin 768) :
    (workerResult a b).stacks (workerStack i)=b.stacks i :=
  embedState_stack id workerStack a b (Fin.castAdd_injective 768 128) i

theorem workerResult_high (a : FrameData) (b : State 40 768) (i : Fin 896)
    (hi : 768 ≤ i.val) : (workerResult a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp only [workerStack,Fin.val_castAdd] at hv
  omega

abbrev exportWorker (src : Fin 768) (dst : Fin 896) : Cmd 40 896 :=
  .seq (route (workerStack src,dst)) clearWorker
noncomputable def exportedWorker (src : Fin 768) (dst : Fin 896) (a : FrameData) : FrameData :=
  workerCleared (routed (workerStack src,dst) a)
def exportCost (src : Fin 768) (dst : Fin 896) (a : FrameData) : ℕ :=
  routeCost (workerStack src,dst) a+
    LeafProgram.Cleanup.Wide.budget (projectState id workerStack (routed (workerStack src,dst) a))+1

theorem exportWorker_eval (src : Fin 768) (hs : src≠767) (dst : Fin 896)
    (hd : 768 ≤ dst.val) (a : FrameData) (ht : a.stacks 767=[]) :
    Eval (exportWorker src dst) (exportCost src dst a) a (exportedWorker src dst a) := by
  have hsd : workerStack src≠dst := by
    intro h; have := congrArg Fin.val h
    simp only [workerStack,Fin.val_castAdd] at this
    have := src.isLt; omega
  have hst : workerStack src≠767 := by
    intro h; apply hs; apply Fin.ext
    exact congrArg (fun x : Fin 896 => x.val) h
  have hdt : dst≠767 := by intro h; subst dst; change 768 ≤ 767 at hd; omega
  have h1 := route_eval (workerStack src,dst) ⟨hsd,hst,hdt⟩ a ht
  have htmp : (routed (workerStack src,dst) a).stacks 767=[] := by
    simpa [routed,Ne.symm hdt] using ht
  simpa only [exportWorker,exportedWorker,exportCost,Nat.add_assoc] using
    h1.seq (clearWorker_eval _ htmp)

theorem exportedWorker_output (src : Fin 768) (dst : Fin 896) (a : FrameData)
    (hd : 768 ≤ dst.val) : (exportedWorker src dst a).stacks dst=a.stacks (workerStack src) := by
  rw [exportedWorker,clearWorker_frame _ dst hd]
  simp [routed]

theorem exportedWorker_empty (src : Fin 768) (dst : Fin 896) (a : FrameData) (i : Fin 768) :
    (exportedWorker src dst a).stacks (workerStack i)=[] := clearWorker_stack _ i

theorem exportedWorker_frame (src : Fin 768) (dst : Fin 896) (a : FrameData)
    (i : Fin 896) (hi : 768 ≤ i.val) (hn : i≠dst) :
    (exportedWorker src dst a).stacks i=a.stacks i := by
  rw [exportedWorker,clearWorker_frame _ i hi]
  simp [routed,hn]

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
