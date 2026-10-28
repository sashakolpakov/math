import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramABI
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram

namespace OAI.Algorithms

/-! Construct the full ambient representative of a bucket tuple by actual
native merges. The complete assignment lists are retained in the saved heads. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput BucketInput rawFrames)
open SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram (merge merge_length)

abbrev Data := State 8 20
abbrev Code := Cmd 8 20

theorem rawFrames_eq_words (xs : List (List Bool)) : rawFrames xs = words xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rawFrames,words,ih]

def state (regs : Fin 8 → Bool) (width outer remaining saved baseline out : List Bool) : Data :=
  ⟨regs, ![outer,remaining,[],[],[],[],[],baseline,out,[],[],[],[],[],[],saved,width,[],[],List.replicate width.length false]⟩

def mergePorts : Fin 10 → Fin 20 := ![6,3,7,4,15,9,10,11,12,13]
theorem mergePorts_injective : Function.Injective mergePorts := by decide

def mergeCall : Code := .call (ProgramLinking.liftProgram
  LeafAssignmentMergeProgram.Native.program id mergePorts)

def headStep : Code :=
  .seq (readWord 1 2 14 (by decide))
  (.seq (readWord 2 3 14 (by decide))
  (.seq (readWord 2 4 14 (by decide))
  (.seq (readWord 2 5 14 (by decide))
  (.seq (readWord 5 6 14 (by decide))
  (.seq (WorkspaceCleanupProgram.command 0 1 [4,5])
  (.seq mergeCall
  (.seq (WorkspaceCleanupProgram.command 0 1 [3,6,7])
        (move 13 7 14))))))))

def headCost (h : HeadInput) (n : ℕ) : ℕ :=
  9*h.bits.length + 11*h.context.length + 9*(rawFrames h.assignments).length +
  2*(rawFrames h.assignments.tail).length + 60*n+78

theorem headStep_eval (regs : Fin 8 → Bool)
    (width outer tail saved baseline out rep : List Bool) (rest : List (List Bool))
    (mask context : List Bool) (hm : mask.length=rep.length) (hb : baseline.length=rep.length) :
    ∃ rf, Eval headStep (headCost ⟨mask,context,rep::rest⟩ rep.length)
      (state regs width outer (Encoding.frame (HeadInput.bits ⟨mask,context,rep::rest⟩)++tail) saved baseline out)
      (state rf width outer tail saved (merge rep mask baseline) out) := by
  let head : HeadInput := ⟨mask,context,rep::rest⟩
  let d := state regs width outer (Encoding.frame head.bits++tail) saved baseline out
  obtain ⟨a,ha,hsa⟩ := readWord_eval (1 : Fin 20) 2 14
    (by decide) (by decide) (by decide) d head.bits tail rfl rfl rfl
  obtain ⟨b,hbr,hsb⟩ := readWord_eval (2 : Fin 20) 3 14
    (by decide) (by decide) (by decide) a mask
    (Encoding.frame context++Encoding.frame (rawFrames (rep::rest)))
    (by simp [hsa,head,HeadInput.bits,List.append_assoc])
    (by simp [hsa,d,state]) (by simp [hsa,d,state])
  obtain ⟨c,hc,hsc⟩ := readWord_eval (2 : Fin 20) 4 14
    (by decide) (by decide) (by decide) b context (Encoding.frame (rawFrames (rep::rest)))
    (by simp [hsb]) (by simp [hsb,hsa,d,state]) (by simp [hsb,hsa,d,state])
  obtain ⟨e,he,hse⟩ := readWord_eval (2 : Fin 20) 5 14
    (by decide) (by decide) (by decide) c (rawFrames (rep::rest)) []
    (by simp [hsc]) (by simp [hsc,hsb,hsa,d,state]) (by simp [hsc,hsb,hsa,d,state])
  obtain ⟨f,hf,hsf⟩ := readWord_eval (5 : Fin 20) 6 14
    (by decide) (by decide) (by decide) e rep (rawFrames rest)
    (by simp [hse,rawFrames]) (by simp [hse,hsc,hsb,hsa,d,state])
    (by simp [hse,hsc,hsb,hsa,d,state])
  let g := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([4,5] : List (Fin 20)) f
  have hg := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([4,5] : List (Fin 20)) (by decide) f
  have hp : projectState id mergePorts g = LeafAssignmentMergeProgram.Native.data
      g.regs rep mask baseline [] saved [] [] [] [] := by
    apply congrArg (StructuredProgram.State.mk g.regs)
    funext i; fin_cases i <;>
      simp [mergePorts,
        LeafWeightProgram.Native.tapes,g,hsf,hse,hsc,hsb,hsa,d,state
        ]
  obtain ⟨rh,hh⟩ := LeafAssignmentMergeProgram.Native.program_trace g.regs rep mask baseline
    [] saved hm.symm hb.symm
  rw [←hp] at hh
  have hcall := eval_call_from_state LeafAssignmentMergeProgram.Native.program id mergePorts g
    Function.injective_id mergePorts_injective hh
  let h := embedState id mergePorts g (LeafAssignmentMergeProgram.Native.data
    rh rep mask baseline [] saved [] [] [] (merge rep mask baseline))
  have hsh : h.stacks = Function.update g.stacks 13 (merge rep mask baseline) := by
    have heq : h = ⟨rh,Function.update g.stacks 13 (merge rep mask baseline)⟩ := by
      apply embedState_eq_of_ports id mergePorts g _ _ Function.injective_id mergePorts_injective
      · intro i; rfl
      · intro i hi; exact (hi ⟨i,rfl⟩).elim
      · intro i; fin_cases i <;>
          simp [mergePorts,
            LeafWeightProgram.Native.tapes,g,hsf,hse,hsc,hsb,hsa,d,state
            ]
      · intro i hi
        have hi13 : i≠13 := by intro heq; subst i; exact hi ⟨9,rfl⟩
        simp [hi13]
    exact congrArg StructuredProgram.State.stacks heq
  change Eval mergeCall (30*rep.length+22) g h at hcall
  let i := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([3,6,7] : List (Fin 20)) h
  have hi := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([3,6,7] : List (Fin 20)) (by decide) h
  obtain ⟨j,hj,hsj⟩ := move_eval (13 : Fin 20) 7 14
    (by decide) (by decide) (by decide) i
    (by simp [i])
    (by simp [i,hsh,g,hsf,hse,hsc,hsb,hsa,d,state])
  have hend : j = state j.regs width outer tail saved (merge rep mask baseline) out := by
    apply congrArg (StructuredProgram.State.mk j.regs)
    funext k; fin_cases k <;>
      simp [hsj,i,hsh,g,hsf,hse,hsc,hsb,hsa,d,state]
  have hall := ha.seq (hbr.seq (hc.seq (he.seq (hf.seq (hg.seq (hcall.seq (hi.seq hj)))))))
  change Eval headStep _ d j at hall
  rw [hend] at hall
  refine ⟨j.regs, ?_⟩
  convert hall using 1
  simp [headCost,head,WorkspaceCleanupProgram.cost,i,hsh,g,hsf,hse,hsc,hsb,hsa,
    d,state,hm,hb,rawFrames,merge_length]
  ; omega

/-- Every attained bucket is inhabited and has the ambient width. -/
def Valid (n : ℕ) (h : HeadInput) : Prop :=
  ∃ rep rest, h.assignments=rep::rest ∧ rep.length=n ∧ h.mask.length=n

def representative (heads : List HeadInput) (baseline : List Bool) : List Bool :=
  heads.foldl (fun acc h => merge (h.assignments.headD []) h.mask acc) baseline

def headsBits (heads : List HeadInput) : List Bool := rawFrames (heads.map HeadInput.bits)

def peek : Code := .base (.atom (.peek 1 0 1))
def ready (regs : Fin 8 → Bool) (width outer remaining saved baseline out : List Bool) : Data :=
  state (readRegs regs 0 1 remaining.head?) width outer remaining saved baseline out

def headLoop : Code := .while 1 (.seq headStep peek)
def headCommand : Code := .seq peek headLoop

def headsCost (heads : List HeadInput) (n : ℕ) : ℕ :=
  (heads.map (fun h => headCost h n+2)).sum+1

theorem peek_eval (regs : Fin 8 → Bool) (width outer remaining saved baseline out : List Bool) :
    Eval peek 1 (state regs width outer remaining saved baseline out)
      (ready regs width outer remaining saved baseline out) := by
  exact .base (.atom _ _)

theorem representative_length (heads : List HeadInput) (baseline : List Bool) (n : ℕ)
    (hv : ∀ h∈heads,Valid n h) (hb : baseline.length=n) :
    (representative heads baseline).length=n := by
  induction heads generalizing baseline with
  | nil => exact hb
  | cons h hs ih =>
      obtain ⟨rep,rest,ha,hr,hm⟩ := hv h (by simp)
      apply ih _ (fun x hx => hv x (by simp [hx]))
      simp [ha,hr]

theorem headLoop_eval (regs : Fin 8 → Bool) (width outer saved baseline out : List Bool)
    (heads : List HeadInput) (n : ℕ) (hv : ∀ h∈heads,Valid n h) (hb : baseline.length=n) :
    ∃ rf, Eval headLoop (headsCost heads n)
      (ready regs width outer (headsBits heads) saved baseline out)
      (state rf width outer [] saved (representative heads baseline) out) := by
  induction heads generalizing regs baseline with
  | nil =>
      refine ⟨(ready regs width outer (headsBits []) saved baseline out).regs, ?_⟩
      simpa [headLoop, headsCost, headsBits, ready, state, representative] using
        (Eval.while_false (show (ready regs width outer (headsBits []) saved baseline out).regs 1=false by
          simp [ready,state,headsBits,readRegs]) : Eval headLoop 1 _ _)
  | cons h hs ih =>
      obtain ⟨rep,rest,ha,hr,hm⟩ := hv h (by simp)
      have heq : h=⟨h.mask,h.context,rep::rest⟩ := by cases h; simp_all
      obtain ⟨rm,hem⟩ := headStep_eval
        (ready regs width outer (headsBits (h::hs)) saved baseline out).regs
        width outer (headsBits hs) saved baseline out rep rest h.mask h.context
        (by omega) (by omega)
      rw [←heq,hr] at hem
      have hstart : state (ready regs width outer (headsBits (h::hs)) saved baseline out).regs
          width outer (Encoding.frame h.bits++headsBits hs) saved baseline out =
          ready regs width outer (headsBits (h::hs)) saved baseline out := rfl
      rw [hstart] at hem
      obtain ⟨rf,hef⟩ := ih rm (merge rep h.mask baseline)
        (fun x hx => hv x (by simp [hx])) (by simp [hr])
      have hg : (ready regs width outer (headsBits (h::hs)) saved baseline out).regs 1=true := by
        cases hx : h.bits <;> simp [ready,state,headsBits,hx,Encoding.frame,readRegs]
      have hall := Eval.while_true hg (hem.seq (peek_eval rm width outer (headsBits hs) saved _ out)) hef
      refine ⟨rf, ?_⟩
      convert hall using 1
      · rfl
      · simp [headsCost]
        omega
      · simp [representative, ha]

theorem headCommand_eval (regs : Fin 8 → Bool) (width outer saved baseline out : List Bool)
    (heads : List HeadInput) (n : ℕ) (hv : ∀ h∈heads,Valid n h) (hb : baseline.length=n) :
    ∃ rf, Eval headCommand (headsCost heads n+1)
      (state regs width outer (headsBits heads) saved baseline out)
      (state rf width outer [] saved (representative heads baseline) out) := by
  obtain ⟨rf,hf⟩ := headLoop_eval regs width outer saved baseline out heads n hv hb
  exact ⟨rf, by
    simpa [headCommand, Nat.add_comm] using
      (peek_eval regs width outer (headsBits heads) saved baseline out).seq hf⟩

/-- The executed merge fold has the expected ambient-coordinate meaning. -/
theorem representative_ofFn {n : ℕ} (heads : List HeadInput)
    (mask rep : HeadInput → Fin n → Bool) (baseline : Fin n → Bool)
    (hm : ∀ h∈heads,h.mask=List.ofFn (mask h))
    (hr : ∀ h∈heads,h.assignments.headD []=List.ofFn (rep h)) :
    representative heads (List.ofFn baseline) =
      List.ofFn (heads.foldl (fun acc h i => if mask h i then rep h i else acc i) baseline) := by
  induction heads generalizing baseline with
  | nil => rfl
  | cons h hs ih =>
      change representative hs (merge (h.assignments.headD []) h.mask (List.ofFn baseline)) = _
      rw [hr h (by simp),hm h (by simp),LeafAssignmentMergeProgram.merge_ofFn]
      exact ih _ (fun x hx=>hm x (by simp [hx])) (fun x hx=>hr x (by simp [hx]))

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

end OAI.Algorithms
