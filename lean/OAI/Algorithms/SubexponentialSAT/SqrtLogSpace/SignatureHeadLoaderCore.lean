import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramCompatibility
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

def entry : Cmd 16 256 :=
  LayoutFiberSumProgram.command LayoutProgram.EntryBank.command

def matrixInputs : List (Fin 768 × Fin 288) :=
  [(141,0),(650,17),(128,18),(651,23),
   (135,225),(136,226),(640,227),(641,228),(140,229),(642,230),
   (138,231),(139,232),(130,233),(131,234),(307,235),(132,236),(647,281)]
theorem matrixInputs_protected : ∀ p∈matrixInputs,Protected p.1 := by
  simp [matrixInputs,Protected,temporary]
def matrixBase (a : Data) : Fin 288 → List Bool := fun i =>
  if i=0 then a.stacks 141 else if i=17 then a.stacks 650 else if i=18 then a.stacks 128 else
  if i=23 then a.stacks 651 else if i=225 then a.stacks 135 else if i=226 then a.stacks 136 else
  if i=227 then a.stacks 640 else if i=228 then a.stacks 641 else if i=229 then a.stacks 140 else
  if i=230 then a.stacks 642 else if i=231 then a.stacks 138 else if i=232 then a.stacks 139 else
  if i=233 then a.stacks 130 else if i=234 then a.stacks 131 else if i=235 then a.stacks 307 else
  if i=236 then a.stacks 132 else []

theorem matrix_prepared (a : Data) (D : ℕ) (hD : a.stacks 647=List.replicate D true) :
    projectState id (workPort (by decide)) (prepared (by decide) matrixInputs a)=
      LayoutMatrixProgram.initialState (matrixBase a) (prepared (by decide) matrixInputs a).regs D := by
  apply prepared_eq id (by decide) matrixInputs a _ matrixInputs_protected (by decide)
  · intro j; rfl
  · intro p hp
    simp only [matrixInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [LayoutMatrixProgram.initialState,LayoutMatrixProgram.state,matrixBase,hD]
  · intro j hj
    simp only [matrixInputs,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at hj
    rcases hj with ⟨h0,h17,h18,h23,h225,h226,h227,h228,h229,h230,h231,h232,h233,h234,h235,h236,h281⟩
    simp [LayoutMatrixProgram.initialState,LayoutMatrixProgram.state,matrixBase, *]



theorem prepare_nonoutput_length (a : Data) (rp : Fin 8 → Bool)
    (n N : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) (i : Fin 768)
    (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
    ((preparedHead a rp n N rows low W z).stacks i).length ≤ (a.stacks i).length := by
  let b := headResult a n rows low W z
  let c := countResult b
  let d := scatterResult c rp n (selectedHeads n rows low z)
  have hb : (b.stacks i).length ≤ (a.stacks i).length :=
    returned_nonoutput_length_le id (by decide) headInputs headOutputs a _ i
      (by simp [headOutputs,h650,h651])
  have hc : (c.stacks i).length ≤ (b.stacks i).length :=
    returned_nonoutput_length_le countRegs (by decide) countInputs countOutputs b _ i
      (by simp [countOutputs,h652])
  have hd : (d.stacks i).length ≤ (c.stacks i).length :=
    returned_nonoutput_length_le scatterRegs (by decide) scatterInputs scatterOutputs c _ i
      (by simp [scatterOutputs,h670])
  have he : ((factorResult d n N rows W z).stacks i).length ≤ (d.stacks i).length :=
    returned_nonoutput_length_le id (by decide) factorInputs factorOutputs d _ i
      (by simp [factorOutputs,h671])
  exact he.trans (hd.trans (hc.trans hb))

/-- Exactly the physical source words read by head selection and native
integer entries. Unrelated arithmetic scratch is deliberately excluded. -/
def masters : List (Fin 768) :=
  [128,129,130,131,132,133,134,135,136,138,139,140,141,307,640,641,642,647]
structure MasterFrame (base b : Data) : Prop where
  stored : ∀ i∈masters,b.stacks i=base.stacks i

theorem matrixEntry_prepared_master (base b : Data) (hf : MasterFrame base b)
    (rp : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (regs : Fin 16 → Bool) (row col pos neg : List Bool) :
    LayoutMatrixProgram.entryState (matrixBase (preparedHead b rp n N rows low W z))
      regs row col pos neg=
    LayoutMatrixProgram.entryState (matrixBase base) regs row col pos neg := by
  have hs (i : Fin 768) (hi : Protected i) (hm : i∈masters)
      (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
      (preparedHead b rp n N rows low W z).stacks i=base.stacks i :=
    (preparedHead_frame b rp n N rows low W z i hi h650 h651 h652 h670 h671).trans
      (hf.stored i hm)
  have h135 := hs 135 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h136 := hs 136 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h640 := hs 640 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h641 := hs 641 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h140 := hs 140 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h642 := hs 642 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h138 := hs 138 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h139 := hs 139 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h130 := hs 130 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h131 := hs 131 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h307 := hs 307 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h132 := hs 132 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply congrArg (StructuredProgram.State.mk regs)
  funext i
  have hn (j : Fin 288) (hj : j.val < 25) : LayoutMatrixProgram.bankPort i≠j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [LayoutMatrixProgram.bankPort] at hv
    omega
  simp only [matrixBase, hn 0 (by decide), hn 17 (by decide), hn 18 (by decide),
    hn 23 (by decide), h135, h136, h640, h641, h140, h642, h138, h139, h130,
    h131, h307, h132, ite_false]

theorem entryContract_prepared_master (entry : Cmd 16 256) (base b : Data) (hf : MasterFrame base b)
    (rp : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : LayoutMatrixProgram.EntryContract entry (matrixBase base) Valid Rel T B) :
    LayoutMatrixProgram.EntryContract entry (matrixBase (preparedHead b rp n N rows low W z))
      Valid Rel T B := by
  intro regs j v hv
  simpa only [matrixEntry_prepared_master base b hf rp n N W z rows low] using hc regs j v hv

/-- Raw matrix output; the old bucket output21 is never selected. -/
def rawOutputs : List (Fin 288 × Fin 768) := [(24,669)]
def rawCommand : Code :=
  stage (LayoutMatrixProgram.program entry) id (by decide) matrixInputs rawOutputs

def shiftRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def shiftInputs : List (Fin 768 × Fin 17) := [(141,0),(669,14)]
def shiftOutputs : List (Fin 17 × Fin 768) := [(15,668)]
def shiftCommand : Code :=
  stage BucketProgram.preMatrixProgram shiftRegs (by decide) shiftInputs shiftOutputs

/-- The low bank computes a single actual head; output668 is the full shifted
matrix. Raw669 is cleared before returning to the signature iterator. -/
def localCommand : Code :=
  .seq prepareHead (.seq rawCommand (.seq shiftCommand (clearCmd 669)))
def localProgram := compiled localCommand 649 668

theorem rawOutputs_protected : ∀ p∈rawOutputs,Protected p.2 := by
  simp [rawOutputs,Protected,temporary]

theorem shiftInputs_protected : ∀ p∈shiftInputs,Protected p.1 := by
  simp [shiftInputs,Protected,temporary]

theorem shiftOutputs_protected : ∀ p∈shiftOutputs,Protected p.2 := by
  simp [shiftOutputs,Protected,temporary]

/-- A local polynomial run gives a polynomial bound for every paid stage,
including input copies, dirty work-bank clearing, and output copies. -/
theorem stage_trace_bound {r q l t T A : ℕ} (p : Program r q l)
    (reg : Fin r → Fin 16) (hs : q ≤ 288)
    (ins : List (Fin 768 × Fin q)) (outs : List (Fin q × Fin 768))
    (a : Data) (b : State r q)
    (hi : ∀ v∈ins,Protected v.1) (ho : ∀ v∈outs,Protected v.2)
    (hdi : (ins.map Prod.snd).Nodup) (hdo : (outs.map Prod.snd).Nodup)
    (ha : WordBound A a) (ht : t ≤ T)
    (tr : Trace p t
      ((projectState reg (workPort hs) (prepared hs ins a)).withPC (some p.entry))
      (b.withPC none)) :
    stageCost reg hs ins outs a b t ≤ T+(6*q+7*ins.length+10*outs.length+21)*(A+T+1) ∧
    WordBound (A+T) (returned reg hs ins outs a b) := by
  have hp := prepared_wordBound hs ins a A hi hdi ha
  have hb : WordBound (A+T) b := by
    intro i
    have h := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le tr i
    change (b.stacks i).length ≤ ((prepared hs ins a).stacks (workPort hs i)).length + t at h
    exact h.trans (Nat.add_le_add (hp _) ht)
  have ha' : WordBound (A+T) a := fun i => (ha i).trans (Nat.le_add_right _ _)
  refine ⟨?_,returned_wordBound reg hs ins outs a b (A+T) hi ho hdi hdo ha' hb⟩
  exact (stageCost_linear reg hs ins outs a b t (A+T) hi ho hdi hdo ha' hb).trans
    (Nat.add_le_add_right ht _)

/-- Paid raw-matrix staging, with its exact physical output and caller frame.
The native specialization below discharges the entry contract. -/
theorem raw_eval (a : Data) (D n : ℕ) (js : List ℕ)
    (hD : a.stacks 647=List.replicate D true)
    (hi : a.stacks 650=LayoutMatrixProgram.ids js)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (T B : ℕ)
    (hc : LayoutMatrixProgram.EntryContract entry (matrixBase a) Valid Rel T B)
    (hv : ∀ j<D,∀ v∈js,Valid j v) (hjs : ∀ v∈js,v ≤ n) :
    ∃ rf rows t,
      LayoutMatrixProgram.MatrixRel Rel B D js rows ∧
      t ≤ stageCost id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)
        (LayoutMatrixProgram.commandCost T B D n js+1) ∧
      Eval rawCommand t a (returned id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)) ∧
      (returned id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)).stacks 669=
          LayoutMatrixProgram.rowsWords rows ∧
      ∀ A,WordBound A a →
        t ≤ (LayoutMatrixProgram.commandCost T B D n js+1)+
          1878*(A+(LayoutMatrixProgram.commandCost T B D n js+1)+1) ∧
        WordBound (A+(LayoutMatrixProgram.commandCost T B D n js+1))
          (returned id (by decide) matrixInputs rawOutputs a
            (LayoutMatrixProgram.finalState (matrixBase a) rf rows)) := by
  obtain ⟨rf,rows,⟨t,ht,he⟩,hr⟩ := LayoutMatrixProgram.program_runsIn entry
    (matrixBase a) (by simp [matrixBase]) (by simp [matrixBase]) Valid Rel T B hc
    D n js (by simpa [matrixBase] using hi) hv hjs
    (prepared (by decide) matrixInputs a).regs
  have hs := stage_eval (LayoutMatrixProgram.program entry) id Function.injective_id
    (by decide) matrixInputs rawOutputs a _ _ matrixInputs_protected rawOutputs_protected
    (matrix_prepared a D hD) he
  refine ⟨rf,rows,_,hr,?_,hs,?_,?_⟩
  · unfold stageCost
    omega
  · exact returned_word id (by decide) matrixInputs rawOutputs a _
      rawOutputs_protected (by decide) (24,669) (by simp [rawOutputs])
  · intro A ha
    have hex := he
    rw [←matrix_prepared a D hD] at hex
    have hb := stage_trace_bound (LayoutMatrixProgram.program entry) id
      (by decide) matrixInputs rawOutputs a _ matrixInputs_protected rawOutputs_protected
      (by decide) (by decide) ha ht hex
    simpa only [matrixInputs,rawOutputs,List.length_cons,List.length_nil] using hb

/-- Exact projection into the 17-stack preprocessing machine. -/
theorem shift_prepared (a : Data) (rows : List (List BucketProgram.SignedWord))
    (hr : a.stacks 669=LayoutMatrixProgram.rowsWords rows) :
    projectState shiftRegs (workPort (by decide)) (prepared (by decide) shiftInputs a)=
      BucketProgram.preMatrixState ((prepared (by decide) shiftInputs a).regs ∘ shiftRegs)
        (a.stacks 141) rows [] := by
  apply prepared_eq shiftRegs (by decide) shiftInputs a _ shiftInputs_protected (by decide)
  · intro j
    rfl
  · intro p hp
    simp only [shiftInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · simp [BucketProgram.preMatrixState]
    · simp [BucketProgram.preMatrixState,hr,LayoutMatrixProgram.rowsWords_eq]
  · intro j hj
    have h0 : j≠0 := hj (141,0) (by simp [shiftInputs])
    have h14 : j≠14 := hj (669,14) (by simp [shiftInputs])
    fin_cases j <;> simp_all [BucketProgram.preMatrixState]

/-- Paid shift staging reads the physically emitted signed rows. -/
theorem shift_eval (a : Data) (rows : List (List BucketProgram.SignedWord))
    (hr : a.stacks 669=LayoutMatrixProgram.rowsWords rows) :
    ∃ rf ys t,
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) rows ys ∧
      t ≤ stageCost shiftRegs (by decide) shiftInputs shiftOutputs a
        (BucketProgram.preMatrixState rf (a.stacks 141) []
          (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))
        (BucketProgram.preMatrixCost (a.stacks 141) rows+1) ∧
      Eval shiftCommand t a (returned shiftRegs (by decide) shiftInputs shiftOutputs a
        (BucketProgram.preMatrixState rf (a.stacks 141) []
          (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))) ∧
      (returned shiftRegs (by decide) shiftInputs shiftOutputs a
        (BucketProgram.preMatrixState rf (a.stacks 141) []
          (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))).stacks 668=
            Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words) ∧
      ∀ A L h,WordBound A a → (a.stacks 141).length ≤ L →
        (∀ row∈rows,BucketProgram.preWordsBounded L row ∧ row.length ≤ h) →
        let work := 10000*(rows.length+1)*(h+1)*(L+1)^2
        t ≤ work+147*(A+work+1) ∧
        WordBound (A+work) (returned shiftRegs (by decide) shiftInputs shiftOutputs a
          (BucketProgram.preMatrixState rf (a.stacks 141) []
            (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)))) := by
  obtain ⟨rf,ys,⟨t,ht,he⟩,hy⟩ := BucketProgram.preMatrixProgram_runsIn
    ((prepared (by decide) shiftInputs a).regs ∘ shiftRegs) (a.stacks 141) rows
  have hs := stage_eval BucketProgram.preMatrixProgram shiftRegs (Fin.castAdd_injective _ _)
    (by decide) shiftInputs shiftOutputs a _ _ shiftInputs_protected shiftOutputs_protected
    (shift_prepared a rows hr) he
  refine ⟨rf,ys,_,hy,?_,hs,?_,?_⟩
  · unfold stageCost
    omega
  · exact returned_word shiftRegs (by decide) shiftInputs shiftOutputs a _
      shiftOutputs_protected (by decide) (15,668) (by simp [shiftOutputs])
  · intro A L h ha hW hb
    have htime := ht.trans (BucketProgram.preMatrixCost_polynomial (a.stacks 141) rows L h hW hb)
    have hex := he
    rw [←shift_prepared a rows hr] at hex
    have hh := stage_trace_bound BucketProgram.preMatrixProgram shiftRegs
      (by decide) shiftInputs shiftOutputs a _ shiftInputs_protected shiftOutputs_protected
      (by decide) (by decide) ha htime hex
    simpa only [shiftInputs,shiftOutputs,List.length_cons,List.length_nil] using hh

/-- State of the paid one-head loader, before its high-bank export. -/
def localResult (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) : Data :=
  let preparedHeadState := preparedHead a rp n N rows low W z
  let rawState := returned id (by decide) matrixInputs rawOutputs preparedHeadState
    (LayoutMatrixProgram.finalState (matrixBase preparedHeadState) rm raw)
  clearState 669 (returned shiftRegs (by decide) shiftInputs shiftOutputs rawState
    (BucketProgram.preMatrixState rs (rawState.stacks 141) []
      (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words))))

/-- The budget includes every stage and the final raw-word clear. -/
def localBudget (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (T B D : ℕ) : ℕ :=
  let p := preparedHead a rp n N rows low W z
  let mlocal := LayoutMatrixProgram.finalState (matrixBase p) rm raw
  let m := returned id (by decide) matrixInputs rawOutputs p mlocal
  let slocal := BucketProgram.preMatrixState rs (m.stacks 141) []
    (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words))
  let e := returned shiftRegs (by decide) shiftInputs shiftOutputs m slocal
  prepareHeadCost a rp n N rows low W z+
    (stageCost id (by decide) matrixInputs rawOutputs p mlocal
      (LayoutMatrixProgram.commandCost T B D n (selectedHeads n rows low z)+1)+
    (stageCost shiftRegs (by decide) shiftInputs shiftOutputs m slocal
      (BucketProgram.preMatrixCost (m.stacks 141) raw+1)+(2*(e.stacks 669).length+3)))

/-- Every persistent protected source except the head outputs and matrix
output668 is retained by the local loader. -/
theorem localResult_frame (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (hi : Protected i)
    (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h668 : i≠668)
    (h669 : i≠669) (h670 : i≠670) (h671 : i≠671) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks i=a.stacks i := by
  unfold localResult
  simp only [clearState,Function.update_of_ne h669]
  rw [returned_frame shiftRegs (by decide) shiftInputs shiftOutputs _ _ i hi
    (by simpa [shiftOutputs] using h668)]
  rw [returned_frame id (by decide) matrixInputs rawOutputs _ _ i hi
    (by simpa [rawOutputs] using h669)]
  exact preparedHead_frame a rp n N rows low W z i hi h650 h651 h652 h670 h671

/-- The selected head identifiers, size, mask and factor context survive
both matrix stages in their original dedicated tapes. -/
theorem localResult_head (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (hi : i∈([650,651,670,671] : List (Fin 768))) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks i=
      (preparedHead a rp n N rows low W z).stacks i := by
  have hp : Protected i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> decide
  have h668 : i≠668 := by intro h; subst i; simp at hi
  have h669 : i≠669 := by intro h; subst i; simp at hi
  unfold localResult
  simp only [clearState,Function.update_of_ne h669]
  rw [returned_frame shiftRegs (by decide) shiftInputs shiftOutputs _ _ i hp
    (by simpa [shiftOutputs] using h668)]
  exact returned_frame id (by decide) matrixInputs rawOutputs _ _ i hp
    (by simpa [rawOutputs] using h669)

theorem localResult_outputs (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    let e := localResult a rp rm rs n N W z rows low raw shifted
    let js := selectedHeads n rows low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        Encoding.encodeNat) := by
  dsimp only
  rw [localResult_head a rp rm rs n N W z rows low raw shifted 650 (by decide),
    localResult_head a rp rm rs n N W z rows low raw shifted 651 (by decide),
    localResult_head a rp rm rs n N W z rows low raw shifted 670 (by decide),
    localResult_head a rp rm rs n N W z rows low raw shifted 671 (by decide)]
  exact ⟨preparedHead_ids ..,preparedHead_count ..,preparedHead_mask ..,preparedHead_context ..⟩

theorem localResult_masters (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    MasterFrame a (localResult a rp rm rs n N W z rows low raw shifted) := by
  constructor
  intro i hi
  simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    exact localResult_frame a rp rm rs n N W z rows low raw shifted _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Non-output stacks never grow across reloads, including dirty arithmetic
scratch. This endpoint fact prevents retained storage from compounding across
an exponential number of generator calls. -/
theorem localResult_nonoutput_length (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652)
    (h668 : i≠668) (h670 : i≠670) (h671 : i≠671) :
    ((localResult a rp rm rs n N W z rows low raw shifted).stacks i).length ≤
      (a.stacks i).length := by
  by_cases h669 : i=669
  · subst i
    simp [localResult,clearState]
  let p := preparedHead a rp n N rows low W z
  let m := returned id (by decide) matrixInputs rawOutputs p
    (LayoutMatrixProgram.finalState (matrixBase p) rm raw)
  have hp := prepare_nonoutput_length a rp n N rows low W z i
    h650 h651 h652 h670 h671
  have hm := returned_nonoutput_length_le id (by decide) matrixInputs rawOutputs
    p (LayoutMatrixProgram.finalState (matrixBase p) rm raw) i
    (by simpa [rawOutputs] using h669)
  have hs := returned_nonoutput_length_le shiftRegs (by decide) shiftInputs shiftOutputs m
    (BucketProgram.preMatrixState rs (m.stacks 141) []
      (Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words))) i
    (by simpa [shiftOutputs] using h668)
  simpa only [localResult,clearState,Function.update_of_ne h669,p,m] using hs.trans (hm.trans hp)

private theorem forallTwo_member {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {y : β} (hy : y∈ys) :
    ∃ x∈xs,R x y := by
  induction h with
  | nil => simp at hy
  | cons hxy ht ih =>
      rcases List.mem_cons.mp hy with rfl|hy
      · exact ⟨_,by simp,hxy⟩
      · obtain ⟨x,hx,hr⟩ := ih hy
        exact ⟨x,by simp [hx],hr⟩

theorem raw_pair_bounds {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows) :
    ∀ row∈rows,BucketProgram.preWordsBounded B row := by
  intro row hrow p hp
  obtain ⟨j,_,hjr⟩ := forallTwo_member hr hrow
  obtain ⟨v,_,hvp⟩ := forallTwo_member hjr hp
  have hlen := hvp.2
  unfold LayoutMatrixProgram.pairLength at hlen
  exact ⟨by omega,by omega⟩

/-- The retained shifted matrix has D rows and every original head column.
Its size depends on physical coefficient word lengths, not their integer values. -/
theorem shifted_matrix_word_length (W : List Bool) {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    {ys : List (List (List Bool))}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows ys) :
    (Subexp.MatrixProgramSupport.words (ys.map Subexp.MatrixProgramSupport.words)).length ≤
      D*(12*js.length*(B+W.length)+6*js.length+1) := by
  have hpairs := raw_pair_bounds hr
  obtain ⟨hrows,hwrows⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hinputs := BucketProgram.preMatrix_inputs W rows (B+W.length) js.length
    (Nat.le_add_left _ _) (by
      intro row hrow
      refine ⟨?_,(hwrows row hrow).le⟩
      intro pair hpair
      have h := hpairs row hrow pair hpair
      exact ⟨h.1.trans (Nat.le_add_right _ _),h.2.trans (Nat.le_add_right _ _)⟩)
  obtain ⟨hlen,hpayload⟩ := BucketProgram.shiftedMatrix_lengths hy
  rw [BucketProgram.preWords_length,List.length_map,←hlen,hrows]
  rw [hrows] at hinputs
  nlinarith [hinputs.2]

/-- The physical shifted rows retain every incidence and the exact emitted
column order, including empty matrices and empty heads. -/
theorem shiftedMatrix_typed (W : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (B D : ℕ)
    (js : List ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys) :
    ∃ c : Fin D → Fin js.length → List Bool,
      ys = List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i, ∃ p, Rel j.val (js.get i) p ∧
        LayoutMatrixProgram.pairLength p ≤ B ∧ BucketProgram.shiftedWord W p (c j i) := by
  obtain ⟨hlen, hrow⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hylen : ys.length = D := hy.length_eq.symm.trans hlen
  have hyrow : ∀ row ∈ ys, row.length = js.length :=
    BucketProgram.shiftedMatrix_rowWidth hy js.length hrow
  let rowAt (j : Fin D) : List (List Bool) := ys.get ⟨j.val, by omega⟩
  have hrowAt (j : Fin D) : (rowAt j).length = js.length :=
    hyrow _ (List.get_mem _ _)
  let c (j : Fin D) (i : Fin js.length) : List Bool :=
    (rowAt j).get ⟨i.val, by rw [hrowAt]; exact i.isLt⟩
  refine ⟨c, ?_, ?_⟩
  · apply List.ext_get
    · simp [hylen]
    · intro j hj hj'
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      apply List.ext_get
      · simp [← hrowAt ⟨j, by simpa using hj'⟩, rowAt]
      · intro i hi hi'
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        rfl
  · intro j i
    have hjraw : j.val < raw.length := by omega
    have hjrange : j.val < (List.range D).length := by simp
    have hrawrow := hr.get hjrange hjraw
    simp only [List.get_eq_getElem, List.getElem_range] at hrawrow
    have hshiftrow := hy.get hjraw (by omega)
    have hiraw : i.val < (raw.get ⟨j.val,hjraw⟩).length := by
      change i.val < (raw[j.val]'hjraw).length
      rw [← hrawrow.length_eq]
      exact i.isLt
    have hiy : i.val < (ys.get ⟨j.val,by omega⟩).length := by
      exact (hrowAt j).symm ▸ i.isLt
    have hp := hrawrow.get i.isLt hiraw
    have hs := hshiftrow.get hiraw hiy
    exact ⟨_, hp.1, hp.2, hs⟩


theorem localResult_countWord (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks 652 =
      List.replicate (selectedHeads n rows low z).length true := by
  unfold localResult
  simp only [clearState, Function.update_of_ne (by decide : (652 : Fin 768) ≠ 669)]
  rw [returned_frame shiftRegs (by decide) shiftInputs shiftOutputs _ _ 652
    (by decide) (by simp [shiftOutputs])]
  rw [returned_frame id (by decide) matrixInputs rawOutputs _ _ 652
    (by decide) (by simp [rawOutputs])]
  rw [preparedHead, factorResult_frame _ _ _ _ _ _ 652 (by decide) (by decide),
    scatterResult_frame _ _ _ _ 652 (by decide) (by decide), countResult_value,
    headResult_count]
  simp [zeros, selectedHeads, HeadIdentifierProgram.count]

theorem localResult_matrixWord (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks 668 =
      Subexp.MatrixProgramSupport.words (shifted.map Subexp.MatrixProgramSupport.words) := by
  unfold localResult
  simp only [clearState, Function.update_of_ne (by decide : (668 : Fin 768) ≠ 669)]
  exact returned_word shiftRegs (by decide) shiftInputs shiftOutputs _ _
    shiftOutputs_protected (by decide) (15,668) (by simp [shiftOutputs])

def retainedOutputBound (n N D B L : ℕ) : ℕ :=
  n * (2*n+2) + 2 + (2*N+2)*N + D*(12*n*(B+L)+6*n+1)

/-- A fixed output envelope is reused at every head reload; caller storage
enters only through max, not through a recurrent enlargement. -/
theorem localResult_retained_bound (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z A D B L : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (ha : WordBound A a) (hW : (a.stacks 141).length ≤ L)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D (selectedHeads n rows low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (a.stacks 141))) raw shifted) :
    WordBound (max A (retainedOutputBound n N D B L))
      (localResult a rp rm rs n N W z rows low raw shifted) := by
  obtain ⟨h650,h651,h670,h671⟩ := localResult_outputs a rp rm rs n N W z rows low raw shifted
  have hj : (selectedHeads n rows low z).length ≤ n := Bounds.selectedHeads_length n rows low z
  have hsmall : n ≤ retainedOutputBound n N D B L := by
    have hn : n ≤ n*(2*n+2) := by
      calc
        n = n*1 := (Nat.mul_one _).symm
        _ ≤ n*(2*n+2) := Nat.mul_le_mul_left n (by omega)
    unfold retainedOutputBound
    omega
  have hmatrix := shifted_matrix_word_length (a.stacks 141) hr hy
  have hproduct : 12*(selectedHeads n rows low z).length*(B+(a.stacks 141).length) ≤
      12*n*(B+L) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 12 hj) (Nat.add_le_add_left hW B)
  have hm : (Subexp.MatrixProgramSupport.words
      (shifted.map Subexp.MatrixProgramSupport.words)).length ≤
      D*(12*n*(B+L)+6*n+1) := hmatrix.trans (Nat.mul_le_mul_left D (by omega))
  have hmax : retainedOutputBound n N D B L ≤ max A (retainedOutputBound n N D B L) :=
    Nat.le_max_right _ _
  intro i
  by_cases hi : i = 650
  · subst i
    rw [h650]
    exact (HeadIdentifierProgram.encodedIds_length_bound
      (HeadIdentifierProgram.predicate rows low z) n).trans (by
        apply le_trans _ hmax
        unfold retainedOutputBound
        omega)
  by_cases hi' : i = 651
  · subst i
    rw [h651, List.length_replicate]
    exact (hj.trans hsmall).trans hmax
  by_cases hi'' : i = 652
  · subst i
    rw [localResult_countWord, List.length_replicate]
    exact (hj.trans hsmall).trans hmax
  by_cases hm' : i = 668
  · subst i
    rw [localResult_matrixWord]
    exact hm.trans (by apply le_trans _ hmax; unfold retainedOutputBound; omega)
  by_cases hh : i = 670
  · subst i
    rw [h670, HeadScatterProgram.mask_length n (selectedHeads n rows low z) _
      (HeadIdentifierProgram.chosenIds_bound (HeadIdentifierProgram.predicate rows low z) n)]
    exact hsmall.trans hmax
  by_cases hf : i = 671
  · subst i
    rw [h671]
    exact (LeafHeadFactorsProgram.encodedIds_length_bound
      (LeafHeadFactorsProgram.predicate rows n z) N).trans (by
        apply le_trans _ hmax
        unfold retainedOutputBound
        omega)
  exact ((localResult_nonoutput_length a rp rm rs n N W z rows low raw shifted i
    hi hi' hi'' hm' hh hf).trans (ha i)).trans (Nat.le_max_left _ _)


/-- Every physical raw-matrix work tape is blank at the loader boundary. -/
theorem localResult_work_empty (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (j : Fin 288) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks (workPort (by decide) j)=[] := by
  have hne (q : Fin 768) (hq : 628 ≤ q.val) : workPort (by decide) j≠q := by
    intro h
    have hv := congrArg Fin.val h
    change 340+j.val=q.val at hv
    have := j.isLt
    omega
  unfold localResult
  simp only [clearState,Function.update_of_ne (hne 669 (by decide))]
  rw [returned_nonoutput_eq shiftRegs (by decide) shiftInputs shiftOutputs _ _ _
    (by simpa [shiftOutputs] using hne 668 (by decide))]
  split_ifs
  · rfl
  · rw [returned_nonoutput_eq id (by decide) matrixInputs rawOutputs _ _ _
      (by simpa [rawOutputs] using hne 669 (by decide))]
    simp only [Or.inl (work_mem_workPorts (by decide) j), ite_true]

/-- The paid staging copy temporary is restored to blank. -/
theorem localResult_temporary_empty (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks 659=[] := by
  unfold localResult
  simp only [clearState,Function.update_of_ne (by decide : (659:Fin 768)≠669)]
  rw [returned_nonoutput_eq shiftRegs (by decide) shiftInputs shiftOutputs _ _ 659
    (by simp [shiftOutputs])]
  simp [temporary]

/-- The final leaf ABI reserves the high query controls; only16 registers are
used by the loader and its paid copies. -/
def leafRegs : Fin 16 ↪ Fin 40 := Fin.castAddEmb 24
def lowStacks : Fin 768 ↪ Fin 896 := Fin.castAddEmb 128

def lowCall : Cmd 16 896 :=
  .call (ProgramLinking.liftProgram localProgram id lowStacks)

def importAddress : Cmd 16 896 :=
  .seq (clearMany [649,659,846,847]) (copyCmd 845 649 659)
def exportMatrix : Cmd 16 896 :=
  .seq (clearCmd 659) (.seq (copyCmd 668 847 659) (clearMany [668,669,846]))
def command : Cmd 16 896 := .seq importAddress (.seq lowCall exportMatrix)
def smallProgram := compiled command 845 847
def program := ProgramLinking.liftProgram smallProgram leafRegs id

def addressState (a : State 16 896) : State 16 896 :=
  copyState 845 649 (clearManyState [649,659,846,847] a)
def exportedState (a : State 16 896) : State 16 896 :=
  clearManyState [668,669,846] (copyState 668 847 (clearState 659 a))

theorem importAddress_eval (a : State 16 896) :
    Eval importAddress (clearManyCost [649,659,846,847] a+7*(a.stacks 845).length+5)
      a (addressState a) := by
  have hc := clearMany_eval [649,659,846,847] a
  have hp := copy_eval 845 649 659 (clearManyState [649,659,846,847] a)
    (by decide) (by decide) (by decide) (by simp [clearMany_stacks])
  simpa only [importAddress, addressState, clearMany_stacks,
    show (845:Fin 896)∉[649,659,846,847] by decide, ite_false, Nat.add_assoc]
    using hc.seq hp

theorem exportMatrix_eval (a : State 16 896) :
    Eval exportMatrix
      (2*(a.stacks 659).length+3+(7*(a.stacks 668).length+5+
        clearManyCost [668,669,846] (copyState 668 847 (clearState 659 a))))
      a (exportedState a) := by
  have hc := clear_eval 659 a
  have hp := copy_eval 668 847 659 (clearState 659 a)
    (by decide) (by decide) (by decide) (by simp [clearState])
  have he := clearMany_eval [668,669,846] (copyState 668 847 (clearState 659 a))
  simpa only [exportMatrix, exportedState, clearState,
    Function.update_of_ne (by decide : (668:Fin 896)≠659)]
    using hc.seq (hp.seq he)

theorem exportedState_matrix (a : State 16 896) (h847 : a.stacks 847=[]) :
    (exportedState a).stacks 847=a.stacks 668 := by
  simp [exportedState,clearMany_stacks,copyState,clearState,StackRoutines.copyStacks,h847]

theorem exportedState_raw (a : State 16 896) : (exportedState a).stacks 846=[] := by
  simp [exportedState,clearMany_stacks]

theorem exportedState_frame (a : State 16 896) (i : Fin 896)
    (hi : i≠659 ∧ i≠668 ∧ i≠669 ∧ i≠846 ∧ i≠847) :
    (exportedState a).stacks i=a.stacks i := by
  simp only [exportedState,clearMany_stacks,List.mem_cons,
    List.not_mem_nil,hi.2.1,hi.2.2.1,hi.2.2.2.1,or_self]
  rw [copyState_frame _ _ _ _ hi.2.2.2.2]
  simp [clearState,hi.1]

def importCost (a : State 16 896) : ℕ :=
  clearManyCost [649,659,846,847] a+7*(a.stacks 845).length+5

def exportCost (a : State 16 896) : ℕ :=
  2*(a.stacks 659).length+3+(7*(a.stacks 668).length+5+
    clearManyCost [668,669,846] (copyState 668 847 (clearState 659 a)))

def lowResult (a : State 16 896) (b : Data) : State 16 896 :=
  embedState id lowStacks (addressState a) b

theorem command_eval (a : State 16 896) (b : Data) (steps : ℕ)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressState a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    Eval command (importCost a+(steps+exportCost (lowResult a b))) a
      (exportedState (lowResult a b)) := by
  have hl := eval_call_from_state localProgram id lowStacks (addressState a)
    Function.injective_id lowStacks.injective ht
  exact (importAddress_eval a).seq (hl.seq (exportMatrix_eval (lowResult a b)))

theorem command_trace (a : State 16 896) (b : Data) (steps : ℕ)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressState a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    Trace smallProgram (importCost a+(steps+exportCost (lowResult a b))+1)
      (a.withPC (some smallProgram.entry)) ((exportedState (lowResult a b)).withPC none) :=
  compiled_halt_trace (command_eval a b steps ht) 845 847

/-- A successful native head reload is promoted to the exact final40-register
leaf ABI, including all address and matrix copying instructions. -/
theorem leaf_eval (frame : State 40 896) (a : State 16 896) (b : Data) (steps : ℕ)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressState a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    Eval (.call program) (importCost a+(steps+exportCost (lowResult a b))+1)
      (embedState leafRegs id frame a)
      (embedState leafRegs id frame (exportedState (lowResult a b))) :=
  eval_call_lifted smallProgram leafRegs id frame leafRegs.injective
    Function.injective_id (command_trace a b steps ht)

theorem lowResult_matrix (a : State 16 896) (b : Data) :
    (exportedState (lowResult a b)).stacks 847=b.stacks 668 := by
  rw [exportedState_matrix]
  · exact embedState_stack id lowStacks _ b lowStacks.injective 668
  · unfold lowResult
    rw [embedState_stack_frame id lowStacks _ b 847 (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      change j.val=847 at hv
      have := j.isLt
      omega)]
    simp [addressState,copyState,StackRoutines.copyStacks,clearMany_stacks]

theorem lowResult_controls (a : State 16 896) (b : Data) (i : Fin 896)
    (hlo : 836 ≤ i.val) (hhi : i.val ≤ 845) :
    (exportedState (lowResult a b)).stacks i=a.stacks i := by
  have hn (j : Fin 896) (hj : j.val<836 ∨ 845<j.val) : i≠j := by
    intro he
    have hv := congrArg Fin.val he
    omega
  rw [exportedState_frame _ i ⟨hn 659 (by decide),hn 668 (by decide),
    hn 669 (by decide),hn 846 (by decide),hn 847 (by decide)⟩]
  unfold lowResult
  rw [embedState_stack_frame id lowStacks _ b i (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega)]
  rw [addressState,copyState_frame _ _ _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega),clearMany_stacks]
  have hnot : i∉([649,659,846,847] : List (Fin 896)) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hn 649 (by decide),hn 659 (by decide),hn 846 (by decide),hn 847 (by decide)⟩
  simp only [hnot, ite_false]

theorem addressState_wordBound (a : State 16 896) (A : ℕ) (ha : WordBound A a) :
    WordBound A (addressState a) := by
  have hc := clearMany_wordBound [649,659,846,847] a A ha
  intro i
  by_cases hi : i=649
  · subst i
    simpa [addressState,copyState,StackRoutines.copyStacks,clearMany_stacks] using ha 845
  · simpa only [addressState,copyState_frame _ _ _ _ hi] using hc i

theorem importCost_le (a : State 16 896) (A : ℕ) (ha : WordBound A a) :
    importCost a ≤ 15*A+17 := by
  have hc := clearManyCost_le [649,659,846,847] a A ha
  have hw := ha 845
  simp only [List.length_cons,List.length_nil] at hc
  unfold importCost
  omega

theorem exportCost_le (a : State 16 896) (A : ℕ) (ha : WordBound A a) :
    exportCost a ≤ 21*A+17 := by
  have hc := clearState_wordBound 659 a A ha
  have hp : WordBound (2*A) (copyState 668 847 (clearState 659 a)) := by
    intro i
    by_cases hi : i=847
    · subst i
      simp only [copyState,StackRoutines.copyStacks,Function.update_self,List.length_append]
      exact (Nat.add_le_add (hc 668) (hc 847)).trans (by omega)
    · exact (copyState_frame _ _ _ _ hi ▸ hc i).trans (by omega)
  have hf := clearManyCost_le [668,669,846] _ (2*A) hp
  have h659 := ha 659
  have h668 := ha 668
  simp only [List.length_cons,List.length_nil] at hf
  unfold exportCost
  omega

/-- The native local execution and both paid ABI transfers share this exact
halted trace. Every stack is charged at every prefix of the complete loader. -/
theorem command_run_space (a : State 16 896) (b : Data) (steps T A : ℕ)
    (ha : WordBound A a) (htime : steps ≤ T)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressState a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    ∃ total, total ≤ 36*A+22*T+35 ∧
      Trace smallProgram total (a.withPC (some smallProgram.entry))
        ((exportedState (lowResult a b)).withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace smallProgram prefixSteps (a.withPC (some smallProgram.entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+T+1) := by
  have had := addressState_wordBound a A ha
  have hb : WordBound (A+T) b := by
    intro i
    have h := Subexp.SequentialProgram.trace_stack_length_le ht i
    change (b.stacks i).length ≤ ((addressState a).stacks (lowStacks i)).length+steps at h
    exact h.trans (Nat.add_le_add (had _) htime)
  have had' : WordBound (A+T) (addressState a) :=
    fun i => (had i).trans (Nat.le_add_right _ _)
  have hl : WordBound (A+T) (lowResult a b) :=
    embedState_wordBound id lowStacks (addressState a) b (A+T) lowStacks.injective had' hb
  have himport := importCost_le a A ha
  have hexport := exportCost_le (lowResult a b) (A+T) hl
  let total := importCost a+(steps+exportCost (lowResult a b))+1
  have htotal : total ≤ 36*A+22*T+35 := by dsimp [total]; omega
  refine ⟨total,htotal,command_trace a b steps ht,?_⟩
  have hinput : dataBits (a.withPC (some smallProgram.entry)) ≤ 896*A :=
    StreamResources.dataBits_le_mul _ ha
  intro prefixSteps intermediate hp hpre
  have h := trace_dataBits smallProgram hpre
  omega
/-- The same run and bound after register widening to the actual leaf ABI.
The caller's all896 stacks are included; only the unused registers are framed. -/
theorem leaf_run_space (frame : State 40 896) (a : State 16 896) (b : Data)
    (steps T A : ℕ) (ha : WordBound A a) (htime : steps ≤ T)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressState a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    ∃ total,total ≤ 36*A+22*T+35 ∧
      Trace program total
        ((embedState leafRegs id frame a).withPC (some program.entry))
        ((embedState leafRegs id frame (exportedState (lowResult a b))).withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace program prefixSteps
          ((embedState leafRegs id frame a).withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+T+1) := by
  obtain ⟨total,hbound,htr,_⟩ := command_run_space a b steps T A ha htime ht
  have hl : Trace program total
      ((embedState leafRegs id frame a).withPC (some program.entry))
      ((embedState leafRegs id frame (exportedState (lowResult a b))).withPC none) := by
    simpa [ProgramLinking.embedCfg,ProgramLinking.relocatePc,embedState,
      StructuredProgram.State.withPC,ProgramLinking.liftProgram,program] using
      ProgramLinking.liftProgram_trace smallProgram leafRegs id (frame.withPC none)
        leafRegs.injective Function.injective_id htr
  refine ⟨total,hbound,hl,?_⟩
  have hin : dataBits ((embedState leafRegs id frame a).withPC (some program.entry)) ≤ 896*A := by
    apply StreamResources.dataBits_le_mul
    intro i
    rw [show ((embedState leafRegs id frame a).withPC (some program.entry)).stacks i=
      a.stacks i from embedState_stack leafRegs id frame a Function.injective_id i]
    exact ha i
  intro prefixSteps intermediate hp hpre
  have h := trace_dataBits program hpre
  omega
/-- Exporting the matrix preserves all other retained low-bank outputs. -/
theorem lowResult_low (a : State 16 896) (b : Data) (i : Fin 768)
    (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (exportedState (lowResult a b)).stacks (lowStacks i)=b.stacks i := by
  have hlow (j : Fin 768) (hj : i≠j) : lowStacks i≠lowStacks j :=
    fun h => hj (lowStacks.injective h)
  have hhigh (j : Fin 896) (hj : 768 ≤ j.val) : lowStacks i≠j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=j.val at hv
    have := i.isLt
    omega
  rw [exportedState_frame _ _ ⟨hlow 659 h659,hlow 668 h668,hlow 669 h669,
    hhigh 846 (by decide),hhigh 847 (by decide)⟩]
  exact embedState_stack id lowStacks _ b lowStacks.injective i

/-- All four head descriptors are returned by the concrete40-register loader.
In particular the all-false size word counts every selected ambient ID. -/
theorem leaf_head_outputs (frame : State 40 896) (a : State 16 896) (b : Data)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    let result := localResult b rp rm rs n N W z rows low raw shifted
    let e := embedState leafRegs id frame (exportedState (lowResult a result))
    let js := selectedHeads n rows low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        Encoding.encodeNat) := by
  dsimp only
  have hh := localResult_outputs b rp rm rs n N W z rows low raw shifted
  have hstack (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
      (embedState leafRegs id frame (exportedState (lowResult a
        (localResult b rp rm rs n N W z rows low raw shifted)))).stacks (lowStacks i)=
          (localResult b rp rm rs n N W z rows low raw shifted).stacks i :=
    (embedState_stack leafRegs id frame _ Function.injective_id (lowStacks i)).trans
      (lowResult_low a _ i h659 h668 h669)
  exact ⟨(hstack 650 (by decide) (by decide) (by decide)).trans hh.1,
    (hstack 651 (by decide) (by decide) (by decide)).trans hh.2.1,
    (hstack 670 (by decide) (by decide) (by decide)).trans hh.2.2.1,
    (hstack 671 (by decide) (by decide) (by decide)).trans hh.2.2.2⟩
/-- A fixed alternate address tape supports reverse head visits without
changing the DFS's retained address845. -/
def importAddressFrom (src : Fin 896) : Cmd 16 896 :=
  .seq (clearMany [649,659,846,847]) (copyCmd src 649 659)
def addressStateFrom (src : Fin 896) (a : State 16 896) : State 16 896 :=
  copyState src 649 (clearManyState [649,659,846,847] a)
def commandFrom (src : Fin 896) : Cmd 16 896 :=
  .seq (importAddressFrom src) (.seq lowCall exportMatrix)

/-- The fixed loader's label count is named so callers do not repeatedly
normalize the full structured command merely to compare program types. -/
def programFromLabels (src : Fin 896) : ℕ := size (commandFrom src) + 1

def smallProgramFrom (src : Fin 896) : Program 16 896 (programFromLabels src) := by
  unfold programFromLabels
  exact compiled (commandFrom src) src 847

def programFrom (src : Fin 896) : Program 40 896 (programFromLabels src) :=
  ProgramLinking.liftProgram (smallProgramFrom src) leafRegs id

theorem importAddressFrom_eval (src : Fin 896) (a : State 16 896)
    (hs : src∉([649,659,846,847] : List (Fin 896))) :
    Eval (importAddressFrom src)
      (clearManyCost [649,659,846,847] a+7*(a.stacks src).length+5)
      a (addressStateFrom src a) := by
  have h649 : src≠649 := by intro h; subst src; simp at hs
  have h659 : src≠659 := by intro h; subst src; simp at hs
  have hc := clearMany_eval [649,659,846,847] a
  have hp := copy_eval src 649 659 (clearManyState [649,659,846,847] a)
    h649 h659 (by decide) (by simp [clearMany_stacks])
  simpa only [importAddressFrom, addressStateFrom, clearMany_stacks, hs, ite_false,
    Nat.add_assoc]
    using hc.seq hp

theorem addressStateFrom_value (src : Fin 896) (a : State 16 896)
    (hs : src∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks 649=a.stacks src := by
  simp only [addressStateFrom,copyState,StackRoutines.copyStacks,Function.update_self,
    clearMany_stacks, hs, show (649:Fin 896)∈[649,659,846,847] by decide,
    ite_false, ite_true, List.append_nil]

theorem addressStateFrom_frame (src : Fin 896) (a : State 16 896) (i : Fin 896)
    (hi : i∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks i=a.stacks i := by
  have h649 : i≠649 := by intro h; subst i; simp at hi
  rw [addressStateFrom,copyState_frame _ _ _ _ h649,clearMany_stacks]
  simp only [hi, ite_false]

theorem addressStateFrom_wordBound (src : Fin 896) (a : State 16 896) (A : ℕ)
    (hs : src∉([649,659,846,847] : List (Fin 896))) (ha : WordBound A a) :
    WordBound A (addressStateFrom src a) := by
  have hc := clearMany_wordBound [649,659,846,847] a A ha
  intro i
  by_cases hi : i=649
  · subst i
    rw [addressStateFrom_value src a hs]
    exact ha src
  · simpa only [addressStateFrom,copyState_frame _ _ _ _ hi] using hc i

def lowResultFrom (src : Fin 896) (a : State 16 896) (b : Data) : State 16 896 :=
  embedState id lowStacks (addressStateFrom src a) b

theorem commandFrom_eval (src : Fin 896) (a : State 16 896) (b : Data) (steps : ℕ)
    (hs : src∉([649,659,846,847] : List (Fin 896)))
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressStateFrom src a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    Eval (commandFrom src)
      (clearManyCost [649,659,846,847] a+7*(a.stacks src).length+5+
        (steps+exportCost (lowResultFrom src a b))) a
      (exportedState (lowResultFrom src a b)) := by
  have hl := eval_call_from_state localProgram id lowStacks (addressStateFrom src a)
    Function.injective_id lowStacks.injective ht
  exact (importAddressFrom_eval src a hs).seq
    (hl.seq (exportMatrix_eval (lowResultFrom src a b)))

/-- Reverse visitation has the same paid-copy and native-loader budget. -/
theorem commandFrom_run_space (src : Fin 896) (a : State 16 896) (b : Data)
    (steps T A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896)))
    (ha : WordBound A a) (htime : steps ≤ T)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressStateFrom src a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    ∃ total,total ≤ 36*A+22*T+35 ∧
      Trace (smallProgramFrom src) total (a.withPC (some (smallProgramFrom src).entry))
        ((exportedState (lowResultFrom src a b)).withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace (smallProgramFrom src) prefixSteps
          (a.withPC (some (smallProgramFrom src).entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+T+1) := by
  have had := addressStateFrom_wordBound src a A hs ha
  have hb : WordBound (A+T) b := by
    intro i
    have h := Subexp.SequentialProgram.trace_stack_length_le ht i
    change (b.stacks i).length ≤ ((addressStateFrom src a).stacks (lowStacks i)).length+steps at h
    exact h.trans (Nat.add_le_add (had _) htime)
  have hl : WordBound (A+T) (lowResultFrom src a b) :=
    embedState_wordBound id lowStacks (addressStateFrom src a) b (A+T) lowStacks.injective
      (fun i => (had i).trans (Nat.le_add_right _ _)) hb
  have hc := clearManyCost_le [649,659,846,847] a A ha
  have hsrc := ha src
  have hexport := exportCost_le (lowResultFrom src a b) (A+T) hl
  simp only [List.length_cons,List.length_nil] at hc
  let total := clearManyCost [649,659,846,847] a+7*(a.stacks src).length+5+
    (steps+exportCost (lowResultFrom src a b))+1
  have htotal : total ≤ 36*A+22*T+35 := by dsimp [total]; omega
  refine ⟨total,htotal,compiled_halt_trace (commandFrom_eval src a b steps hs ht) src 847,?_⟩
  have hin : dataBits (a.withPC (some (smallProgramFrom src).entry)) ≤ 896*A :=
    StreamResources.dataBits_le_mul _ ha
  intro prefixSteps intermediate hp hpre
  have hh := trace_dataBits (smallProgramFrom src) hpre
  omega

theorem leafFrom_run_space (src : Fin 896) (frame : State 40 896) (a : State 16 896) (b : Data)
    (steps T A : ℕ) (hs : src∉([649,659,846,847] : List (Fin 896))) (ha : WordBound A a) (htime : steps ≤ T)
    (ht : Trace localProgram steps
      ((projectState id lowStacks (addressStateFrom src a)).withPC (some localProgram.entry))
      (b.withPC none)) :
    ∃ total,total ≤ 36*A+22*T+35 ∧
      Trace (programFrom src) total
        ((embedState leafRegs id frame a).withPC (some (programFrom src).entry))
        ((embedState leafRegs id frame (exportedState (lowResultFrom src a b))).withPC none) ∧
      ∀ prefixSteps intermediate,prefixSteps ≤ total →
        Trace (programFrom src) prefixSteps
          ((embedState leafRegs id frame a).withPC (some (programFrom src).entry)) intermediate →
        dataBits intermediate ≤ 1000*(A+T+1) := by
  obtain ⟨total,hbound,htr,_⟩ := commandFrom_run_space src a b steps T A hs ha htime ht
  have hl : Trace (programFrom src) total
      ((embedState leafRegs id frame a).withPC (some (programFrom src).entry))
      ((embedState leafRegs id frame (exportedState (lowResultFrom src a b))).withPC none) := by
    simpa [ProgramLinking.embedCfg,ProgramLinking.relocatePc,embedState,
      StructuredProgram.State.withPC,ProgramLinking.liftProgram,programFrom] using
      ProgramLinking.liftProgram_trace (smallProgramFrom src) leafRegs id (frame.withPC none)
        leafRegs.injective Function.injective_id htr
  refine ⟨total,hbound,hl,?_⟩
  have hin : dataBits ((embedState leafRegs id frame a).withPC (some (programFrom src).entry)) ≤ 896*A := by
    apply StreamResources.dataBits_le_mul
    intro i
    rw [show ((embedState leafRegs id frame a).withPC (some (programFrom src).entry)).stacks i=
      a.stacks i from embedState_stack leafRegs id frame a Function.injective_id i]
    exact ha i
  intro prefixSteps intermediate hp hpre
  have h := trace_dataBits (programFrom src) hpre
  omega

theorem lowResultFrom_low (src : Fin 896) (a : State 16 896) (b : Data) (i : Fin 768)
    (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (exportedState (lowResultFrom src a b)).stacks (lowStacks i)=b.stacks i := by
  have hlow (j : Fin 768) (hj : i≠j) : lowStacks i≠lowStacks j :=
    fun h => hj (lowStacks.injective h)
  have hhigh (j : Fin 896) (hj : 768 ≤ j.val) : lowStacks i≠j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=j.val at hv
    have := i.isLt
    omega
  rw [exportedState_frame _ _ ⟨hlow 659 h659,hlow 668 h668,hlow 669 h669,
    hhigh 846 (by decide),hhigh 847 (by decide)⟩]
  exact embedState_stack id lowStacks _ b lowStacks.injective i


theorem lowResultFrom_frame (src : Fin 896) (a : State 16 896) (b : Data)
    (i : Fin 896) (hhigh : 768 ≤ i.val)
    (hi : i∉([846,847] : List (Fin 896))) :
    (exportedState (lowResultFrom src a b)).stacks i=a.stacks i := by
  have hn (j : Fin 896) (hj : j.val<768) : i≠j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h846 : i≠846 := by intro h; subst i; simp at hi
  have h847 : i≠847 := by intro h; subst i; simp at hi
  rw [exportedState_frame _ i ⟨hn 659 (by decide),hn 668 (by decide),
    hn 669 (by decide),h846,h847⟩]
  unfold lowResultFrom
  rw [embedState_stack_frame id lowStacks _ b i (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega)]
  apply addressStateFrom_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨hn 649 (by decide),hn 659 (by decide),h846,h847⟩

theorem leafFrom_head_outputs (src : Fin 896) (frame : State 40 896) (a : State 16 896) (b : Data)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    let result := localResult b rp rm rs n N W z rows low raw shifted
    let e := embedState leafRegs id frame (exportedState (lowResultFrom src a result))
    let js := selectedHeads n rows low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        Encoding.encodeNat) := by
  dsimp only
  have hh := localResult_outputs b rp rm rs n N W z rows low raw shifted
  have hstack (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
      (embedState leafRegs id frame (exportedState (lowResultFrom src a
        (localResult b rp rm rs n N W z rows low raw shifted)))).stacks (lowStacks i)=
          (localResult b rp rm rs n N W z rows low raw shifted).stacks i :=
    (embedState_stack leafRegs id frame _ Function.injective_id (lowStacks i)).trans
      (lowResultFrom_low src a _ i h659 h668 h669)
  exact ⟨(hstack 650 (by decide) (by decide) (by decide)).trans hh.1,
    (hstack 651 (by decide) (by decide) (by decide)).trans hh.2.1,
    (hstack 670 (by decide) (by decide) (by decide)).trans hh.2.2.1,
    (hstack 671 (by decide) (by decide) (by decide)).trans hh.2.2.2⟩

/-- The actual lower input reached after the paid address copy. -/
def leafInputFrom (src : Fin 896) (frame : State 40 896) : Data :=
  projectState id lowStacks (addressStateFrom src (projectState leafRegs id frame))

def leafOutputFrom (src : Fin 896) (frame : State 40 896) (b : Data) : State 40 896 :=
  embedState leafRegs id frame
    (exportedState (lowResultFrom src (projectState leafRegs id frame) b))

/-- Export copies into the destination already emptied by address setup. -/
theorem exportedState_wordBound (a : State 16 896) (B : ℕ)
    (h847 : a.stacks 847 = []) (ha : WordBound B a) :
    WordBound B (exportedState a) := by
  apply clearMany_wordBound [668,669,846] _ B
  have hc := clearState_wordBound 659 a B ha
  intro i
  by_cases hi : i = 847
  · subst i
    simpa [copyState, StackRoutines.copyStacks, clearState, h847] using ha 668
  · rw [copyState_frame _ _ _ _ hi]
    exact hc i

theorem lowResultFrom_empty847 (src : Fin 896) (a : State 16 896) (b : Data) :
    (lowResultFrom src a b).stacks 847 = [] := by
  unfold lowResultFrom
  rw [embedState_stack_frame id lowStacks _ b 847 (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 847 at hv
    have := j.isLt
    omega)]
  simp only [addressStateFrom, copyState_frame _ _ _ _
    (by decide : (847 : Fin 896) ≠ 649), clearMany_stacks,
    show (847 : Fin 896) ∈ [649,659,846,847] by decide, ite_true]

theorem exportedLowResultFrom_wordBound (src : Fin 896) (a : State 16 896) (b : Data)
    (A B : ℕ) (hs : src ∉ ([649,659,846,847] : List (Fin 896)))
    (hAB : A ≤ B) (ha : WordBound A a) (hb : WordBound B b) :
    WordBound B (exportedState (lowResultFrom src a b)) := by
  have had := addressStateFrom_wordBound src a A hs ha
  have hl : WordBound B (lowResultFrom src a b) :=
    embedState_wordBound id lowStacks (addressStateFrom src a) b B lowStacks.injective
      (fun i => (had i).trans hAB) hb
  exact exportedState_wordBound _ B (lowResultFrom_empty847 src a b) hl

theorem leafInputFrom_wordBound (src : Fin 896) (frame : State 40 896) (A : ℕ)
    (hs : src ∉ ([649,659,846,847] : List (Fin 896))) (ha : WordBound A frame) :
    WordBound A (leafInputFrom src frame) := by
  have had := addressStateFrom_wordBound src (projectState leafRegs id frame) A hs
    (fun i => ha i)
  intro i
  exact had (lowStacks i)

theorem leafOutputFrom_wordBound (src : Fin 896) (frame : State 40 896) (b : Data)
    (A B : ℕ) (hs : src ∉ ([649,659,846,847] : List (Fin 896)))
    (hAB : A ≤ B) (ha : WordBound A frame) (hb : WordBound B b) :
    WordBound B (leafOutputFrom src frame b) := by
  have he := exportedLowResultFrom_wordBound src (projectState leafRegs id frame) b A B hs hAB
    (fun i => ha i) hb
  intro i
  have hstack : (leafOutputFrom src frame b).stacks i =
      (exportedState (lowResultFrom src (projectState leafRegs id frame) b)).stacks i :=
    embedState_stack leafRegs id frame _ Function.injective_id i
  rw [hstack]
  exact he i


theorem leafInputFrom_masters (src : Fin 896) (frame : State 40 896) (base : Data)
    (hf : MasterFrame base (projectState leafRegs lowStacks frame)) :
    MasterFrame base (leafInputFrom src frame) := by
  constructor
  intro i hi
  have hnot : lowStacks i∉([649,659,846,847] : List (Fin 896)) := by
    simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (addressStateFrom_frame src (projectState leafRegs id frame) (lowStacks i) hnot).trans
    (hf.stored i hi)

/-- Retained source equality composes between concrete call boundaries. -/
theorem MasterFrame.trans {a b c : Data} (hab : MasterFrame a b) (hbc : MasterFrame b c) :
    MasterFrame a c := ⟨fun i hi => (hbc.stored i hi).trans (hab.stored i hi)⟩

theorem leafOutputFrom_masters (src : Fin 896) (frame : State 40 896) (base b : Data)
    (hf : MasterFrame base b) :
    MasterFrame base (projectState leafRegs lowStacks (leafOutputFrom src frame b)) := by
  constructor
  intro i hi
  have hne : i≠659 ∧ i≠668 ∧ i≠669 := by
    simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (embedState_stack leafRegs id frame _ Function.injective_id (lowStacks i)).trans
    ((lowResultFrom_low src (projectState leafRegs id frame) b i hne.1 hne.2.1 hne.2.2).trans
      (hf.stored i hi))

/-- The fixed16-register loader leaves every higher caller register intact. -/
theorem leafOutputFrom_registers (src : Fin 896) (frame : State 40 896) (b : Data)
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (leafOutputFrom src frame b).regs i=frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  have := j.isLt
  omega


/-- The whole shifted matrix is returned on its dedicated physical tape. -/
theorem leafOutputFrom_matrix (src : Fin 896) (frame : State 40 896) (b : Data) :
    (leafOutputFrom src frame b).stacks 847=b.stacks 668 := by
  rw [show (leafOutputFrom src frame b).stacks 847=
    (exportedState (lowResultFrom src (projectState leafRegs id frame) b)).stacks 847 from
      embedState_stack leafRegs id frame _ Function.injective_id 847]
  rw [exportedState_matrix _ (lowResultFrom_empty847 src _ b)]
  exact embedState_stack id lowStacks _ b lowStacks.injective 668

theorem leafOutputFrom_raw_empty (src : Fin 896) (frame : State 40 896) (b : Data) :
    (leafOutputFrom src frame b).stacks 846=[] :=
  (embedState_stack leafRegs id frame _ Function.injective_id 846).trans (exportedState_raw _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
