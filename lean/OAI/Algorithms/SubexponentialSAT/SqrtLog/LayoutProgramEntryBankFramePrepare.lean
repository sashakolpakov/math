import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFrame

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def preparedStacks (a : Data) : Fin 256 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update
  (Function.update a.stacks 42 (a.stacks 202)) 43 (a.stacks 203))
    44 (a.stacks 204)) 45 (a.stacks 205)) 47 (a.stacks 206)) 48 (a.stacks 207))
    21 (a.stacks 208)) 22 (a.stacks 209)) 37 (a.stacks 210)) 26 (a.stacks 211))
    23 (a.stacks 65)) 24 (a.stacks 68)) 25 [true]

theorem prepare_stacks (a : Data) (h : ∀ j : Fin 256, j.val < 64 → a.stacks j=[]) :
    (Staging.result 0 1 prepareOps a).stacks=preparedStacks a := by
  simp [prepareOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,
    TupleProgram.pushedState,preparedStacks,h]

/-- The omitted negative power port really must be empty. This holds for the
unsigned power cache; no such assumption is hidden in the staging program. -/
theorem prepare_project {r Q : ℕ} (a : Data) (c : Numerator.Saved)
    (t : Fin Q) (u y : UniversalType r Q 1)
    (h : ∀ j : Fin 256, j.val < 64 → a.stacks j=[])
    (hp : a.stacks 202=c.hp) (hn : a.stacks 203=c.hn)
    (hw : a.stacks 204=c.width) (hpos : a.stacks 205=c.power.1)
    (hneg : c.power.2=[]) (hr : a.stacks 206=c.r) (ha : a.stacks 207=c.a)
    (hcolors : a.stacks 208=List.replicate r true)
    (hnodes : a.stacks 209=List.replicate Q true)
    (hnode : a.stacks 210=List.replicate t.val true)
    (hwidth : a.stacks 211=List.replicate (Q*r) true)
    (hu : a.stacks 65=CollisionProgram.encodeType u)
    (hy : a.stacks 68=CollisionProgram.encodeType y) :
    projectState integerRegs integerPorts (Staging.result 0 1 prepareOps a)=
      Numerator.state c ((Staging.result 0 1 prepareOps a).regs ∘ integerRegs)
        t u y [] [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  change (Staging.result 0 1 prepareOps a).stacks (integerPorts j)=_
  rw [prepare_stacks a h]
  fin_cases j <;>
    simp [integerPorts,preparedStacks,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,
      hp,hn,hw,hpos,hneg,hr,ha,hcolors,hnodes,hnode,hwidth,hu,hy,h]

theorem integer_lifted (a : Data) {n : ℕ} {b : IntegerEntry.Data}
    (he : Eval IntegerEntry.command n (projectState integerRegs integerPorts a) b) :
    Eval integer (n+1) a (embedState integerRegs integerPorts a b) ∧
    (∀ j : Fin 256, 64 ≤ j.val →
      (embedState integerRegs integerPorts a b).stacks j=a.stacks j) := by
  refine ⟨eval_liftCommand_from_state IntegerEntry.command 23 53 integerRegs integerPorts a
    integerRegs_inj integerPorts_inj he,?_⟩
  intro j hj
  apply embedState_stack_frame
  rintro ⟨i,hi⟩
  have hv := congrArg Fin.val hi
  change i.val=j.val at hv
  omega

/-- Export and cleanup have a single exact endpoint on the entire caller
store, including its unconstrained private bank212..251. -/
theorem export_cleanup_stacks (a : Data) (h254 : a.stacks 254=[])
    (h255 : a.stacks 255=[]) (j : Fin 256) :
    (Staging.result 0 1 cleanupOps (Staging.result 0 1 exportOps a)).stacks j=
      if j.val < 200 then [] else if j=255 then a.stacks 54
        else if j=254 then a.stacks 53 else a.stacks j := by
  rw [cleanup_stacks,exportPair_stacks a h254 h255]
  simp only [Function.update_apply]

theorem export_cleanup_eval (a : Data) (ht : a.stacks 199=[]) :
    Eval (.seq exportPair cleanup)
      (Staging.cost 0 1 exportOps a+
        Staging.cost 0 1 cleanupOps (Staging.result 0 1 exportOps a))
      a (Staging.result 0 1 cleanupOps (Staging.result 0 1 exportOps a)) := by
  exact (exportPair_eval a ht).seq
    (cleanup_eval _ (EntryBankFrame.staging_result_temp 0 1 199 exportOps a exportOps_valid ht))

/-- A complete measured inner entry call. The premise is an actual trace of
the fixed integer command, not a supplied value or a free callback. -/
theorem prepared_integer_export_cleanup (a : Data) (ht : a.stacks 199=[])
    (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[]) {n : ℕ} {b : IntegerEntry.Data}
    (he : Eval IntegerEntry.command n
      (projectState integerRegs integerPorts (Staging.result 0 1 prepareOps a)) b) :
    let p := Staging.result 0 1 prepareOps a
    let q := embedState integerRegs integerPorts p b
    let e := Staging.result 0 1 exportOps q
    let z := Staging.result 0 1 cleanupOps e
    Eval (.seq prepare (.seq integer (.seq exportPair cleanup)))
      (Staging.cost 0 1 prepareOps a+
        ((n+1)+(Staging.cost 0 1 exportOps q+Staging.cost 0 1 cleanupOps e))) a z ∧
    (∀ j : Fin 256, z.stacks j=
      if j.val < 200 then [] else if j=255 then b.stacks 54
        else if j=254 then b.stacks 53 else a.stacks j) := by
  intro p q e z
  obtain ⟨hi,hf⟩ := integer_lifted p he
  have hq : ∀ j : Fin 256, 64 ≤ j.val → q.stacks j=a.stacks j := by
    intro j hj
    exact (hf j hj).trans (prepare_frame a j hj)
  have hqt : q.stacks 199=[] := (hq 199 (by decide)).trans ht
  have hq254 : q.stacks 254=[] := (hq 254 (by decide)).trans h254
  have hq255 : q.stacks 255=[] := (hq 255 (by decide)).trans h255
  refine ⟨(prepare_eval a ht).seq (hi.seq (export_cleanup_eval q hqt)),?_⟩
  intro j
  change (Staging.result 0 1 cleanupOps (Staging.result 0 1 exportOps q)).stacks j=_
  rw [export_cleanup_stacks q hq254 hq255 j]
  have h53 : q.stacks 53=b.stacks 53 :=
    embedState_stack integerRegs integerPorts p b integerPorts_inj 53
  have h54 : q.stacks 54=b.stacks 54 :=
    embedState_stack integerRegs integerPorts p b integerPorts_inj 54
  rw [h53,h54]
  split_ifs with hj hj255 hj254
  · rfl
  · rfl
  · rfl
  · exact hq j (by omega)

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
