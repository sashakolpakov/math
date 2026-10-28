import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramWeightedCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgramBridge

namespace OAI.Algorithms


/-! A raw framed-stream iterator with a mandatory native callback trace.
The invariant observes stacks, allowing the explicit peek instruction to use
scratch Boolean registers. All callback work is included in the bound. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

variable {A W : Type*}

def streamBits (encode : W → List Bool) (xs : List W) : List Bool :=
  rawFrames (xs.map encode)

def scanWork (cost : A → W → ℕ) (step : A → W → A) : A → List W → ℕ
  | _, [] => 1
  | a, x :: xs => cost a x + 2 + scanWork cost step (step a x) xs

/-- This is an explicit integration obligation for a real command. It cannot
be discharged by a semantic operation alone: each record requires an Eval. -/
def BodyContract (src : Fin 768) (body : Code) (encode : W → List Bool)
    (step : A → W → A) (cost : A → W → ℕ)
    (inv : A → (Fin 768 → List Bool) → Prop) : Prop :=
  ∀ a x tail (d : Data), inv a d.stacks →
    d.stacks src = Encoding.frame (encode x) ++ tail →
    ∃ n ≤ cost a x, ∃ e : Data, inv (step a x) e.stacks ∧
      e.stacks src = tail ∧ Eval body n d e

theorem rawLoop_eval (src : Fin 768) (body : Code) (encode : W → List Bool)
    (step : A → W → A) (cost : A → W → ℕ)
    (inv : A → (Fin 768 → List Bool) → Prop)
    (contract : BodyContract src body encode step cost inv)
    (xs : List W) (a : A) (d : Data)
    (hi : inv a d.stacks) (hs : d.stacks src = streamBits encode xs) :
    ∃ n ≤ scanWork cost step a xs, ∃ e : Data,
      inv (xs.foldl step a) e.stacks ∧ e.stacks src = [] ∧
      Eval (rawLoop src body) n (afterPeek d src) e := by
  induction xs generalizing a d with
  | nil =>
      have he : d.stacks src = [] := by simpa [streamBits] using hs
      refine ⟨1, le_rfl, afterPeek d src, ?_, ?_, ?_⟩
      · exact hi
      · exact he
      · exact Eval.while_false (peek_empty d src he)
  | cons x xs ih =>
      have hs' : (afterPeek d src).stacks src =
          Encoding.frame (encode x) ++ streamBits encode xs := by
        simpa [afterPeek, streamBits] using hs
      obtain ⟨n, hn, e, hie, hse, ht⟩ := contract a x (streamBits encode xs)
        (afterPeek d src) hi hs'
      obtain ⟨m, hm, f, hif, hsf, hl⟩ := ih (step a x) e hie hse
      have hne : d.stacks src ≠ [] := by
        rw [hs]
        exact rawFrames_cons_ne (encode x) (xs.map encode)
      have hrun := Eval.while_true (peek_nonempty d src hne)
        (ht.seq (peek_eval e src)) hl
      refine ⟨n+1+m+1, ?_, f, hif, hsf, hrun⟩
      simp only [scanWork]
      omega

/-- Every record is visited by the fixed while-loop and actual callback. -/
theorem rawScan_eval (src : Fin 768) (body : Code) (encode : W → List Bool)
    (step : A → W → A) (cost : A → W → ℕ)
    (inv : A → (Fin 768 → List Bool) → Prop)
    (contract : BodyContract src body encode step cost inv)
    (xs : List W) (a : A) (d : Data)
    (hi : inv a d.stacks) (hs : d.stacks src = streamBits encode xs) :
    ∃ n ≤ scanWork cost step a xs + 1, ∃ e : Data,
      inv (xs.foldl step a) e.stacks ∧ e.stacks src = [] ∧
      Eval (rawScan src body) n d e := by
  obtain ⟨n, hn, e, hie, hse, ht⟩ := rawLoop_eval src body encode step cost inv contract xs a d hi hs
  exact ⟨1+n, by omega, e, hie, hse, (peek_eval d src).seq ht⟩

theorem scanWork_bound (cost : A → W → ℕ) (step : A → W → A) (xs : List W)
    (bound : ℕ) (hcost : ∀ a x, cost a x ≤ bound) (a : A) :
    scanWork cost step a xs ≤ xs.length*(bound+2)+1 := by
  induction xs generalizing a with
  | nil => simp [scanWork]
  | cons x xs ih =>
      have hh := hcost a x
      have ht := ih (step a x)
      simp only [scanWork, List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.MomentsAssembly

/-! Physical nesting of the moment computation. Only the assignment producer
is a parameter: it is supplied as a fixed finite command, with a required Eval
contract in the execution theorem. Scaling, normalization, multiplication,
projection, record parsing, copies, and cleanup are concrete native programs.
The support and head masters are copied by paid loops for each actual use.
-/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def coreRegisters : Fin 8 → Fin 40 := Fin.castAdd 32
def corePorts : Fin 56 → Fin 768 := Fin.castAdd 712

theorem coreRegisters_injective : Function.Injective coreRegisters := Fin.castAdd_injective _ _
theorem corePorts_injective : Function.Injective corePorts := Fin.castAdd_injective _ _

def weightedAdd : Code := liftCommand HashCircuitProgram.WeightedCore.command 41 42
  coreRegisters corePorts

def multiply : Code := .call
  (ProgramLinking.liftProgram MomentsProgram.Product.program coreRegisters corePorts)

def normalize : Code := liftCommand MomentsProgram.Product.normalizePhase 4 42
  coreRegisters corePorts

def projectionRegisters : Fin 5 → Fin 40 := Fin.castAdd 35
def projectionPorts : Fin 10 → Fin 768 := ![40,180,181,182,183,184,185,186,187,188]

theorem projectionRegisters_injective : Function.Injective projectionRegisters :=
  Fin.castAdd_injective _ _
theorem projectionPorts_injective : Function.Injective projectionPorts := by decide

/-- The support mask has already been parsed; scan the dictionary directly. -/
abbrev projectionScan : Cmd 5 10 := .seq (.base (.atom (.peek 0 0 3)))
  (.seq MomentsProjectionProgram.records (MomentsProjectionProgram.transfer 8 9))

def project : Code := liftCommand projectionScan 0 9 projectionRegisters projectionPorts

def moveForward (src dst : Fin 768) : Code :=
  .seq (transfer src 164) (transfer 164 dst)

/-- The producer consumes assignment174, returns scalar44 and dictionary41,
and preserves the current head sum42, head product40, and high contexts. -/
def assignmentStep (produce : Code) : Code :=
  .seq (takeFrame 160 174 (by decide))
    (.seq produce (.seq weightedAdd (clear 41)))

def assignmentScan (produce : Code) : Code := rawScan 160 (assignmentStep produce)

def startHead : Code :=
  .seq (takeFrame 161 176 (by decide))
    (.seq (takeFrame 176 178 (by decide))
      (.seq (takeFrame 176 175 (by decide)) (takeFrame 176 160 (by decide))))

def finishHead : Code :=
  .seq (moveForward 42 41)
    (.seq multiply (.seq (moveForward 42 40)
      (.seq (clear 41) (.seq (clear 175) (clear 178)))))

def headStep (produce : Code) : Code :=
  .seq startHead (.seq (assignmentScan produce) finishHead)

def headScan (produce : Code) : Code := rawScan 161 (headStep produce)

def startSupport : Code :=
  .seq (takeFrame 162 168 (by decide))
    (.seq (copy 167 40) (copy 170 161))

/-- Project the actual product, then add it into the running sparse answer. -/
def finishSupport : Code :=
  .seq (copy 168 164)
    (.seq (transfer 164 180)
      (.seq project (.seq (moveForward 188 4)
        (.seq (moveForward 166 42) (.seq normalize
          (.seq (moveForward 42 166) (.seq (clear 180) (clear 168))))))))

def supportStep (produce : Code) : Code :=
  .seq startSupport (.seq (headScan produce) finishSupport)

def supportScan (produce : Code) : Code := rawScan 162 (supportStep produce)

def startBucket : Code :=
  .seq (takeFrame 163 176 (by decide))
    (.seq (takeFrame 176 177 (by decide))
      (.seq (takeFrame 176 170 (by decide)) (copy 169 162)))

def finishBucket : Code := .seq (clear 177) (clear 170)

def bucketStep (produce : Code) : Code :=
  .seq startBucket (.seq (supportScan produce) finishBucket)

/-- One fixed command for every number of buckets, supports, heads, and
assignments. None of those counts occurs in its finite control. -/
def command (produce : Code) : Code := rawScan 163 (bucketStep produce)

def program (produce : Code) := compiled (command produce) 163 166

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- Replacing the low arithmetic workspace preserves every ambient high tape. -/
noncomputable def coreState (frame : Data) (regs : Fin 8 → Bool) (s : Product.Store) : Data :=
  embedState coreRegisters corePorts frame (Product.state regs s)

theorem coreState_high (frame : Data) (regs : Fin 8 → Bool) (s : Product.Store)
    (i : Fin 768) (hi : 56 ≤ i.val) :
    (coreState frame regs s).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  intro h
  obtain ⟨j, hj⟩ := h
  have hv := congrArg (fun x : Fin 768 => x.val) hj
  simp [corePorts] at hv
  omega

def emptyCore (e : Product.Store) : Product.Store :=
  {e with left := [], right := [], acc := []}

@[simp] theorem working_empty {n B d : ℕ} (e : Product.Store) :
    Product.working e ([] : List (Product.Entry n B d)) [] [] = emptyCore e := rfl

def weightedStore (e : Product.Store) (left seed jet weight : List Bool) : Product.Store :=
  {e with left := left, acc := seed, right := jet, coeff := weight}

def weightedBudget (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d)) : ℕ :=
  25*(Product.bytes jet).length + 11*(RingProgram.flat weight).length + 9*d +
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex jet +
    Normalize.work p t M cache Squarefree.encodeIndex
      (Squarefree.ScaleProgram.scaled p t M cache table weight jet) seed + 44

/-- The wide head worker executes the concrete scale and normalize programs.
The current product on40 and all ambient high tapes are preserved. -/
theorem weightedAdd_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left : List Bool)
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d))
    (frame : Data) (regs : Fin 8 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ weightedBudget p t M cache table weight jet seed, ∃ rr,
      Eval weightedAdd k
        (coreState frame regs (weightedStore e left (Product.bytes seed)
          (Product.bytes jet) (RingProgram.flat weight)))
        (coreState frame rr (weightedStore e left
          (Product.bytes (weightedValue p t M cache table weight jet seed))
          (Product.bytes jet) [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let a := weightedStore e left (Product.bytes seed) (Product.bytes jet) (RingProgram.flat weight)
  obtain ⟨k, hk, rr, he⟩ := HashCircuitProgram.WeightedCore.command_eval p t M cache hz table
    weight degree width hd hw Squarefree.encodeIndex Squarefree.encodeIndex_injective
    jet seed regs a rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hh := eval_liftCommand he 41 42 coreRegisters corePorts frame
    coreRegisters_injective corePorts_injective
  refine ⟨k+1, ?_, rr, ?_⟩
  · simpa [weightedBudget, a, weightedStore, e, Product.environment, Product.idle, hd]
      using Nat.add_le_add_right hk 1
  · simpa only [weightedAdd, coreState, a, weightedStore, weightedValue] using hh

/-- Concrete multiplication of the current product by the completed head. -/
theorem multiply_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (frame : Data) (regs : Fin 8 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ Product.work p t M cache table u J left right []+2, ∃ rr,
      Eval multiply k
        (coreState frame regs (Product.working e left right []))
        (coreState frame rr (Product.working e [] right
          (Product.run p t M cache table u J left right []))) := by
  dsimp only
  obtain ⟨rr, k, hk, ht⟩ := Product.program_run_seed p t M cache hz table degree width hd hw
    u J left right [] regs
  have he := eval_call_lifted Product.program coreRegisters corePorts frame
    coreRegisters_injective corePorts_injective ht
  exact ⟨k, hk, rr, he⟩

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The support mask is already available from the outer loop. The native
projection scans every dictionary record and returns the retained records. -/
theorem projectionScan_eval (es : List MomentsProjectionProgram.Entry)
    (regs : Fin 5 → Bool) (query : List Bool) :
    ∃ n ≤ MomentsProjectionProgram.loopBudget query es +
      3*(MomentsProjectionProgram.raw (MomentsProjectionProgram.selected query es)).length+4,
      ∃ rr, Eval projectionScan n
        (MomentsProjectionProgram.machine regs
          (MomentsProjectionProgram.clean (MomentsProjectionProgram.raw es) query []))
        (MomentsProjectionProgram.machine rr
          {target := query.reverse,
           framed := MomentsProjectionProgram.raw (MomentsProjectionProgram.selected query es)}) := by
  let source := MomentsProjectionProgram.raw es
  let output := MomentsProjectionProgram.raw (MomentsProjectionProgram.selected query es)
  have hp : Eval (.base (.atom (.peek 0 0 3))) 1
      (MomentsProjectionProgram.machine regs (MomentsProjectionProgram.clean source query []))
      (MomentsProjectionProgram.readyRecords regs source query []) := .base (.atom _ _)
  obtain ⟨n, hn, rr, ht⟩ := MomentsProjectionProgram.records_eval es regs query []
  let b : MomentsProjectionProgram.Tape := MomentsProjectionProgram.clean [] query output.reverse
  have ht' : Eval MomentsProjectionProgram.records n
      (MomentsProjectionProgram.readyRecords regs source query [])
      (MomentsProjectionProgram.machine rr b) := by
    simpa only [source, output, b, List.append_nil] using ht
  let c : MomentsProjectionProgram.Tape := {target := query.reverse, framed := output}
  have hf := MomentsProjectionProgram.transfer_machine rr b c 8 9 (by decide) (by
    funext i
    fin_cases i <;> simp [StackRoutines.transferStacks, MomentsProjectionProgram.tapes,
      b, c, MomentsProjectionProgram.clean])
  refine ⟨1+n+(3*output.length+3), by dsimp [output]; omega,
    SubexponentialSAT.BitProgram.readRegs rr 0 1 none, ?_⟩
  simpa [projectionScan, source, output, b, c,
    MomentsProjectionProgram.tapes, MomentsProjectionProgram.clean, List.length_reverse, Nat.add_assoc]
    using hp.seq (ht'.seq hf)

theorem projectionScan_budget (es : List MomentsProjectionProgram.Entry) (query : List Bool) :
    MomentsProjectionProgram.loopBudget query es +
      3*(MomentsProjectionProgram.raw (MomentsProjectionProgram.selected query es)).length+5 ≤
      200*((MomentsProjectionProgram.raw es).length+1)*(query.length+2)+1 := by
  have h1 := MomentsProjectionProgram.loopBudget_bound query es
  have h2 := MomentsProjectionProgram.raw_count es
  have h3 := MomentsProjectionProgram.selected_length query es
  have hm := Nat.mul_le_mul_left (query.length+1) h2
  nlinarith

/-- The actual relocated projection call, preserving all outer loop state. -/
theorem project_eval (es : List MomentsProjectionProgram.Entry)
    (regs : Fin 5 → Bool) (query : List Bool) (frame : Data) :
    ∃ n ≤ 200*((MomentsProjectionProgram.raw es).length+1)*(query.length+2)+1,
      ∃ rr, Eval project n
        (embedState projectionRegisters projectionPorts frame
          (MomentsProjectionProgram.machine regs
            (MomentsProjectionProgram.clean (MomentsProjectionProgram.raw es) query [])))
        (embedState projectionRegisters projectionPorts frame
          (MomentsProjectionProgram.machine rr
            {target := query.reverse,
             framed := MomentsProjectionProgram.raw (MomentsProjectionProgram.selected query es)})) := by
  obtain ⟨n, hn, rr, he⟩ := projectionScan_eval es regs query
  refine ⟨n+1, ?_, rr, ?_⟩
  · exact (Nat.add_le_add_right hn 1).trans (projectionScan_budget es query)
  · exact eval_liftCommand he 0 9 projectionRegisters projectionPorts frame
      projectionRegisters_injective projectionPorts_injective

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def afterMove (d : Data) (src dst : Fin 768) : Data :=
  ⟨SubexponentialSAT.BitProgram.readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src ++ d.stacks dst)⟩

/-- Forward movement is two actual reversing stack transfers. -/
theorem moveForward_eval (d : Data) (src dst : Fin 768)
    (hs : src ≠ 164) (hd : (164 : Fin 768) ≠ dst) (hsd : src ≠ dst)
    (ht : d.stacks 164 = []) :
    Eval (moveForward src dst) (6*(d.stacks src).length+6) d (afterMove d src dst) := by
  have h1 := transfer_eval d src 164 hs
  have h2 := transfer_eval (afterTransfer d src 164) 164 dst hd
  have hh := h1.seq h2
  have hcost : 3 * (d.stacks src).length + 3 +
      (3 * ((afterTransfer d src 164).stacks 164).length + 3) =
      6 * (d.stacks src).length + 6 := by
    simp [ StackRoutines.transferStacks, ht]
    omega
  have hout : afterTransfer (afterTransfer d src 164) 164 dst = afterMove d src dst := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ SubexponentialSAT.BitProgram.readRegs]
    · funext i
      by_cases hi : i = src
      · subst i
        simp [ StackRoutines.transferStacks, hs, hsd,
 Ne.symm hd, Ne.symm hsd, ht]
      by_cases hj : i = dst
      · subst i
        simp [ StackRoutines.transferStacks,
 Ne.symm hd, Ne.symm hsd, ht]
      by_cases hk : i = 164
      · subst i
        simp [ StackRoutines.transferStacks, hd,
          Ne.symm hs, Ne.symm hd, Ne.symm hsd, ht]
      simp [ StackRoutines.transferStacks, hi, hj, hk]
  rw [hcost, hout] at hh
  exact hh

theorem afterTake_stack_frame (d : Data) (src dst i : Fin 768) (bits tail : List Bool)
    (hs : i ≠ src) (hd : i ≠ dst) :
    (afterTake d src dst bits tail).stacks i = d.stacks i := by
  simp [ hs, hd]

theorem afterMove_stack_frame (d : Data) (src dst i : Fin 768)
    (hs : i ≠ src) (hd : i ≠ dst) :
    (afterMove d src dst).stacks i = d.stacks i := by
  simp [afterMove, hs, hd]

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open MomentsProgram

/-- The arithmetic workspace and arbitrary preserved ambient memory. -/
def machine (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) : Data :=
  ⟨regs, fun i => if h : i.val < 56 then Product.tapes core ⟨i.val,h⟩ else high i⟩

def combineRegisters (old : Fin 40 → Bool) (new : Fin 8 → Bool) : Fin 40 → Bool :=
  fun i => if h : i.val < 8 then new ⟨i.val,h⟩ else old i

theorem combineRegisters_self (regs : Fin 40 → Bool) :
    combineRegisters regs (regs ∘ coreRegisters) = regs := by
  funext i
  by_cases hi : i.val < 8
  · simp [combineRegisters, hi, coreRegisters]
  · simp [combineRegisters, hi]

theorem coreState_machine (regs : Fin 40 → Bool) (rr : Fin 8 → Bool)
    (old new : Product.Store) (high : Fin 768 → List Bool) :
    coreState (machine regs old high) rr new =
      machine (combineRegisters regs rr) new high := by
  apply embedState_eq_of_ports _ _ _ _ _ coreRegisters_injective corePorts_injective
  · intro i
    simp [machine, combineRegisters, coreRegisters, Product.state, i.isLt]
  · intro i hi
    have hn : ¬i.val < 8 := by
      intro hh
      exact hi ⟨⟨i.val,hh⟩,Fin.ext rfl⟩
    simp [machine, combineRegisters, hn]
  · intro i
    simp [machine, corePorts, Product.state, i.isLt]
  · intro i hi
    have hn : ¬i.val < 56 := by
      intro hh
      exact hi ⟨⟨i.val,hh⟩,Fin.ext rfl⟩
    simp [machine, hn]

theorem machine_high (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (i : Fin 768) (hi : 56 ≤ i.val) :
    (machine regs core high).stacks i = high i := by
  simp [machine, Nat.not_lt.mpr hi]

theorem machine_core (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (i : Fin 56) :
    (machine regs core high).stacks (corePorts i) = Product.tapes core i := by
  simp [machine, corePorts, i.isLt]

/-- Parsing a high record leaves every arithmetic tape untouched. -/
theorem afterTake_machine (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (src dst : Fin 768)
    (hs : 56 ≤ src.val) (hd : 56 ≤ dst.val) (bits tail : List Bool) :
    afterTake (machine regs core high) src dst bits tail =
      machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) core
        (Function.update (Function.update high src tail) dst bits) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i.val < 56
    · have his : i ≠ src := by intro h; subst i; omega
      have hid : i ≠ dst := by intro h; subst i; omega
      simp [ machine, hi, his, hid]
    · by_cases hid : i = dst
      · subst i
        simp [ machine, hi]
      by_cases his : i = src
      · subst i
        simp [ machine, hi, hid]
      simp [ machine, hi, his, hid]

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open MomentsProgram

def headHigh1 (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :=
  Function.update (Function.update high 161 tail) 176 h.bits
def headHigh2 (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :=
  Function.update (Function.update (headHigh1 high h tail) 176
    (Encoding.frame h.context ++ Encoding.frame (rawFrames h.assignments))) 178 h.mask
def headHigh3 (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :=
  Function.update (Function.update (headHigh2 high h tail) 176
    (Encoding.frame (rawFrames h.assignments))) 175 h.context
def headHigh (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :=
  Function.update (Function.update (headHigh3 high h tail) 176 []) 160 (rawFrames h.assignments)

def headHeaderBudget (h : HeadInput) : ℕ :=
  9*(h.bits.length+h.mask.length+h.context.length+(rawFrames h.assignments).length)+28

/-- All three head fields are read by native frame loops; their sizes are paid. -/
theorem startHead_eval (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool)
    (hsource : high 161 = Encoding.frame h.bits ++ tail)
    (h164 : high 164 = []) (h176 : high 176 = []) (h178 : high 178 = [])
    (h175 : high 175 = []) (h160 : high 160 = []) :
    ∃ rr, Eval startHead (headHeaderBudget h)
      (machine regs core high) (machine rr core (headHigh high h tail)) := by
  let r1 := SubexponentialSAT.BitProgram.readRegs regs 0 1 none
  let r2 := SubexponentialSAT.BitProgram.readRegs r1 0 1 none
  let r3 := SubexponentialSAT.BitProgram.readRegs r2 0 1 none
  let r4 := SubexponentialSAT.BitProgram.readRegs r3 0 1 none
  have h1 := takeFrame_eval (machine regs core high) 161 176 (by decide) (by decide) (by decide)
    h.bits tail (by simpa [machine] using hsource) (by simpa [machine] using h164)
    (by simpa [machine] using h176)
  rw [afterTake_machine regs core high 161 176 (by decide) (by decide)] at h1
  have h1' : Eval (takeFrame 161 176 (by decide)) (9*h.bits.length+7)
      (machine regs core high) (machine r1 core (headHigh1 high h tail)) := h1
  have h2 := takeFrame_eval (machine r1 core (headHigh1 high h tail)) 176 178
    (by decide) (by decide) (by decide) h.mask
    (Encoding.frame h.context ++ Encoding.frame (rawFrames h.assignments))
    (by simp [machine,headHigh1,HeadInput.bits,List.append_assoc])
    (by simp [machine,headHigh1,h164]) (by simp [machine,headHigh1,h178])
  rw [afterTake_machine r1 core (headHigh1 high h tail) 176 178 (by decide) (by decide)] at h2
  have h2' : Eval (takeFrame 176 178 (by decide)) (9*h.mask.length+7)
      (machine r1 core (headHigh1 high h tail))
      (machine r2 core (headHigh2 high h tail)) := h2
  have h3 := takeFrame_eval (machine r2 core (headHigh2 high h tail)) 176 175
    (by decide) (by decide) (by decide) h.context (Encoding.frame (rawFrames h.assignments))
    (by simp [machine,headHigh2]) (by simp [machine,headHigh2,headHigh1,h164])
    (by simp [machine,headHigh2,headHigh1,h175])
  rw [afterTake_machine r2 core (headHigh2 high h tail) 176 175 (by decide) (by decide)] at h3
  have h3' : Eval (takeFrame 176 175 (by decide)) (9*h.context.length+7)
      (machine r2 core (headHigh2 high h tail))
      (machine r3 core (headHigh3 high h tail)) := h3
  have h4 := takeFrame_eval (machine r3 core (headHigh3 high h tail)) 176 160
    (by decide) (by decide) (by decide) (rawFrames h.assignments) []
    (by simp [machine,headHigh3]) (by simp [machine,headHigh3,headHigh2,headHigh1,h164])
    (by simp [machine,headHigh3,headHigh2,headHigh1,h160])
  rw [afterTake_machine r3 core (headHigh3 high h tail) 176 160 (by decide) (by decide)] at h4
  have h4' : Eval (takeFrame 176 160 (by decide)) (9*(rawFrames h.assignments).length+7)
      (machine r3 core (headHigh3 high h tail))
      (machine r4 core (headHigh high h tail)) := h4
  refine ⟨r4, ?_⟩
  convert h1'.seq (h2'.seq (h3'.seq h4')) using 1 <;>
    first | rfl | (unfold headHeaderBudget; omega)

theorem headHigh_assignments (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :
    headHigh high h tail 160 = rawFrames h.assignments := by simp [headHigh]
theorem headHigh_context (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :
    headHigh high h tail 175 = h.context := by simp [headHigh,headHigh3]
theorem headHigh_mask (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :
    headHigh high h tail 178 = h.mask := by simp [headHigh,headHigh3,headHigh2]
theorem headHigh_tail (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :
    headHigh high h tail 161 = tail := by simp [headHigh,headHigh3,headHigh2,headHigh1]

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- The only assembly callback. The assignment is actual runtime data, and
the contract demands a native Eval for its weight and factor-jet construction.
No head sums, head products, or projected moments are callback outputs. -/
def AssignmentContract (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop) : Prop :=
  ∀ c x left seed (high : Fin 768 → List Bool) (regs : Fin 40 → Bool),
    validFrame high → c.Matches high → high 174 = x →
    let e := Product.environment p t M cache table degree width u J
    let value := meaning c x
    ∃ k ≤ cost c x left seed, ∃ rr,
      Eval produce k
        (machine regs (Product.working e left [] seed) high)
        (machine rr (weightedStore e (Product.bytes left) (Product.bytes seed)
          (Product.bytes value.2) (RingProgram.flat value.1))
          (Function.update high 174 []))

theorem weightedAdd_machine_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left : List Bool)
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ weightedBudget p t M cache table weight jet seed, ∃ rr,
      Eval weightedAdd k
        (machine regs (weightedStore e left (Product.bytes seed)
          (Product.bytes jet) (RingProgram.flat weight)) high)
        (machine rr (weightedStore e left
          (Product.bytes (weightedValue p t M cache table weight jet seed))
          (Product.bytes jet) []) high) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let a := weightedStore e left (Product.bytes seed) (Product.bytes jet) (RingProgram.flat weight)
  obtain ⟨k,hk,rr,he⟩ := weightedAdd_eval p t M cache hz table degree width hd hw
    u J left weight jet seed (machine regs a high) (regs ∘ coreRegisters)
  refine ⟨k,hk,combineRegisters regs rr,?_⟩
  simpa only [coreState_machine, combineRegisters_self] using he

theorem clear_right_eval (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) :
    Eval (clear 41) (2*core.right.length+3) (machine regs core high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) {core with right := []} high) := by
  have hc : Product.tapes {core with right := []} = Function.update (Product.tapes core) 41 [] := by
    funext j
    fin_cases j <;> simp [Product.tapes]
  have he := clear_eval (machine regs core high) 41
  rw [show (machine regs core high).stacks 41 = core.right by
    simp [machine, Product.tapes]] at he
  convert he using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i.val < 56
    · let j : Fin 56 := ⟨i.val,hi⟩
      have hij : corePorts j = i := Fin.ext rfl
      rw [← hij]
      have hh := congrFun hc j
      simpa [machine,corePorts,j.isLt,afterClear,StackRoutines.clearStacks,
        Function.update_apply,Fin.ext_iff] using hh
    · have h41 : i ≠ 41 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      simp [machine, hi, StackRoutines.clearStacks, h41]

def assignmentHigh (high : Fin 768 → List Bool) (x tail : List Bool) : Fin 768 → List Bool :=
  Function.update (Function.update high 160 tail) 174 x

def assignmentBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (c : AssignmentContext) (x : List Bool)
    (left seed : List (Product.Entry n (baseWidth p t) d)) : ℕ :=
  9*x.length+7+cost c x left seed+
    weightedBudget p t M cache table (meaning c x).1 (meaning c x).2 seed+
    (2*(Product.bytes (meaning c x).2).length+3)

/-- One assignment is parsed, produced by the paid worker, and immediately
accumulated by native sparse arithmetic. The source jet is then cleared. -/
theorem assignmentStep_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (c : AssignmentContext) (x tail : List Bool)
    (left seed : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hc : c.Matches high) (hsrc : high 160 = Encoding.frame x ++ tail)
    (h174 : high 174 = []) (h164 : high 164 = [])
    (hv : validFrame (assignmentHigh high x tail)) :
    let e := Product.environment p t M cache table degree width u J
    let result := weightedValue p t M cache table (meaning c x).1 (meaning c x).2 seed
    ∃ k ≤ assignmentBudget p t M cache table meaning cost c x left seed, ∃ rr,
      Eval (assignmentStep produce) k
        (machine regs (Product.working e left [] seed) high)
        (machine rr (Product.working e left [] result)
          (Function.update (assignmentHigh high x tail) 174 [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let a := Product.working e left [] seed
  let rh := SubexponentialSAT.BitProgram.readRegs regs 0 1 none
  let high' := assignmentHigh high x tail
  have h1 := takeFrame_eval (machine regs a high) 160 174 (by decide) (by decide) (by decide)
    x tail (by simpa [machine] using hsrc) (by simpa [machine] using h164)
    (by simpa [machine] using h174)
  rw [afterTake_machine regs a high 160 174 (by decide) (by decide)] at h1
  have h1' : Eval (takeFrame 160 174 (by decide)) (9*x.length+7)
      (machine regs a high) (machine rh a high') := h1
  have hc' : c.Matches high' := by
    simpa [AssignmentContext.Matches, high', assignmentHigh] using hc
  obtain ⟨np,hp,rp,he⟩ := contract c x left seed high' rh hv hc'
    (by simp [high',assignmentHigh])
  let outputHigh := Function.update high' 174 []
  obtain ⟨nw,hw',rw,he'⟩ := weightedAdd_machine_eval p t M cache hz table degree width hd hw
    u J (Product.bytes left) (meaning c x).1 (meaning c x).2 seed outputHigh rp
  let result := weightedValue p t M cache table (meaning c x).1 (meaning c x).2 seed
  have hclear := clear_right_eval rw
    (weightedStore e (Product.bytes left) (Product.bytes result) (Product.bytes (meaning c x).2) []) outputHigh
  refine ⟨(9*x.length+7)+(np+(nw+(2*(Product.bytes (meaning c x).2).length+3))),
    ?_, SubexponentialSAT.BitProgram.readRegs rw 0 1 none, ?_⟩
  · dsimp [assignmentBudget]
    omega
  · convert h1'.seq (he.seq (he'.seq hclear)) using 1 <;>
      simp [assignmentStep, e, high', outputHigh, result, weightedStore,
      Product.working, Product.environment, Product.idle, Product.bytes,
      MomentsProgram.Normalize.bytes,
      Squarefree.Program.rawEntries, Squarefree.Program.encodeDictionary]

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def assignmentStream (base : Fin 768 → List Bool) (bits : List Bool) : Fin 768 → List Bool :=
  Function.update (Function.update base 160 bits) 174 []

theorem assignmentHigh_stream (base : Fin 768 → List Bool) (source x tail : List Bool) :
    assignmentHigh (assignmentStream base source) x tail =
      Function.update (Function.update base 160 tail) 174 x := by
  funext i
  by_cases h1 : i = 174
  · subst i; simp [assignmentHigh,assignmentStream]
  by_cases h2 : i = 160
  · subst i; simp [assignmentHigh,assignmentStream]
  simp [assignmentHigh,assignmentStream,h1,h2]

theorem assignmentHigh_finished (base : Fin 768 → List Bool) (source x tail : List Bool) :
    Function.update (assignmentHigh (assignmentStream base source) x tail) 174 [] =
      assignmentStream base tail := by
  rw [assignmentHigh_stream]
  simp [assignmentStream]

def headWork (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (c : AssignmentContext) (left : List (Product.Entry n (baseWidth p t) d)) :
    List (List Bool) → List (Product.Entry n (baseWidth p t) d) → ℕ
  | [], _ => 1
  | x::xs, seed => assignmentBudget p t M cache table meaning cost c x left seed + 2 +
      headWork p t M cache table meaning cost c left xs
        (weightedValue p t M cache table (meaning c x).1 (meaning c x).2 seed)

theorem assignmentLoop_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (c : AssignmentContext) (base : Fin 768 → List Bool)
    (hc : c.Matches base) (htmp : base 164 = [])
    (hv : ∀ source x, validFrame (Function.update (Function.update base 160 source) 174 x))
    (xs : List (List Bool)) (left seed : List (Product.Entry n (baseWidth p t) d))
    (regs : Fin 40 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ headWork p t M cache table meaning cost c left xs seed, ∃ rr,
      Eval (rawLoop 160 (assignmentStep produce)) k
        (afterPeek (machine regs (Product.working e left [] seed)
          (assignmentStream base (rawFrames xs))) 160)
        (machine rr (Product.working e left [] (headRun p t M cache table meaning c xs seed))
          (assignmentStream base [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  induction xs generalizing seed regs with
  | nil =>
      let a := machine regs (Product.working e left [] seed) (assignmentStream base [])
      have hs : a.stacks 160 = [] := by simp [a,machine,assignmentStream]
      refine ⟨1,le_rfl,(afterPeek a 160).regs,?_⟩
      simpa [rawLoop,headRun,a,afterPeek,machine,assignmentStream] using
        (Eval.while_false (body := .seq (assignmentStep produce) (peek 160)) (peek_empty a 160 hs))
  | cons x xs ih =>
      let high := assignmentStream base (rawFrames (x::xs))
      let a := machine regs (Product.working e left [] seed) high
      let r0 := (afterPeek a 160).regs
      let next := weightedValue p t M cache table (meaning c x).1 (meaning c x).2 seed
      have hstart : afterPeek a 160 = machine r0 (Product.working e left [] seed) high := rfl
      obtain ⟨k,hk,r1,hs⟩ := assignmentStep_eval produce p t M cache hz table degree width hd hw
        u J meaning cost validFrame contract c x (rawFrames xs) left seed high r0
        (by simpa [AssignmentContext.Matches,high,assignmentStream] using hc)
        (by simp [high,assignmentStream,rawFrames]) (by simp [high,assignmentStream])
        (by simp [high,assignmentStream,htmp])
        (by simpa [high,assignmentHigh_stream] using hv (rawFrames xs) x)
      have hs' : Eval (assignmentStep produce) k (afterPeek a 160)
          (machine r1 (Product.working e left [] next) (assignmentStream base (rawFrames xs))) := by
        simpa only [hstart, high, assignmentHigh_finished, next] using hs
      obtain ⟨m,hm,rr,hl⟩ := ih next r1
      let b := machine r1 (Product.working e left [] next) (assignmentStream base (rawFrames xs))
      have hne : a.stacks 160 ≠ [] := by
        simpa [a,high,machine,assignmentStream] using rawFrames_cons_ne x xs
      have hrun := Eval.while_true (peek_nonempty a 160 hne) (hs'.seq (peek_eval b 160)) hl
      refine ⟨k+1+m+1,?_,rr,?_⟩
      · simp only [headWork]
        dsimp [next] at hm
        omega
      · simpa only [rawLoop,headRun,next,a,high,b] using hrun

/-- A complete paid traversal of one head's actual assignment records. -/
theorem assignmentScan_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (c : AssignmentContext) (base : Fin 768 → List Bool)
    (hc : c.Matches base) (htmp : base 164 = [])
    (hv : ∀ source x, validFrame (Function.update (Function.update base 160 source) 174 x))
    (xs : List (List Bool)) (left seed : List (Product.Entry n (baseWidth p t) d))
    (regs : Fin 40 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ headWork p t M cache table meaning cost c left xs seed+1, ∃ rr,
      Eval (assignmentScan produce) k
        (machine regs (Product.working e left [] seed) (assignmentStream base (rawFrames xs)))
        (machine rr (Product.working e left [] (headRun p t M cache table meaning c xs seed))
          (assignmentStream base [])) := by
  dsimp only
  obtain ⟨k,hk,rr,he⟩ := assignmentLoop_eval produce p t M cache hz table degree width hd hw
    u J meaning cost validFrame contract c base hc htmp hv xs left seed regs
  exact ⟨1+k,by omega,rr,(peek_eval _ 160).seq he⟩

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- A low-workspace move is still implemented by the two paid stack scans. -/
theorem move_core_eval (regs : Fin 40 → Bool) (a b : Product.Store)
    (high : Fin 768 → List Bool) (src dst : Fin 56) (hsd : src ≠ dst)
    (ht : high 164 = [])
    (hb : Product.tapes b = Function.update (Function.update (Product.tapes a) src []) dst
      (Product.tapes a src ++ Product.tapes a dst)) :
    Eval (moveForward (corePorts src) (corePorts dst))
      (6*(Product.tapes a src).length+6) (machine regs a high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) b high) := by
  have hs : corePorts src ≠ 164 := by
    intro h
    have hv := congrArg Fin.val h
    simp [corePorts] at hv
    omega
  have hd : (164 : Fin 768) ≠ corePorts dst := by
    intro h
    have hv := congrArg Fin.val h
    simp [corePorts] at hv
    omega
  have hn := fun h => hsd (corePorts_injective h)
  have he := moveForward_eval (machine regs a high) (corePorts src) (corePorts dst)
    hs hd hn (by simpa [machine] using ht)
  convert he using 1
  · simp [machine_core]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 56
      · let j : Fin 56 := ⟨i.val,hi⟩
        have hij : corePorts j = i := Fin.ext rfl
        rw [← hij]
        have hh := congrFun hb j
        simpa [machine, afterMove, corePorts, j.isLt, src.isLt, dst.isLt, Function.update_apply,Fin.ext_iff] using hh
      · have his : i ≠ corePorts src := by
          intro h
          subst i
          exact hi src.isLt
        have hid : i ≠ corePorts dst := by
          intro h
          subst i
          exact hi dst.isLt
        simp [machine, hi, his, hid]

/-- Clearing a high metadata tape preserves the entire arithmetic workspace. -/
theorem clear_high_eval (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (src : Fin 768) (hs : 56 ≤ src.val) :
    Eval (clear src) (2*(high src).length+3) (machine regs core high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) core (Function.update high src [])) := by
  have he := clear_eval (machine regs core high) src
  convert he using 1
  · simp [machine, Nat.not_lt.mpr hs]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 56
      · have his : i ≠ src := by intro h; subst i; omega
        simp [machine,StackRoutines.clearStacks,hi,his]
      · simp [machine,StackRoutines.clearStacks,hi,Function.update_apply]

theorem multiply_machine_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ Product.work p t M cache table u J left right []+2, ∃ rr,
      Eval multiply k (machine regs (Product.working e left right []) high)
        (machine rr (Product.working e [] right (Product.run p t M cache table u J left right [])) high) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  obtain ⟨k,hk,rr,he⟩ := multiply_eval p t M cache hz table degree width hd hw u J
    left right (machine regs (Product.working e left right []) high) (regs ∘ coreRegisters)
  exact ⟨k,hk,combineRegisters regs rr,by
    simpa only [coreState_machine,combineRegisters_self] using he⟩

def finishedHeadHigh (high : Fin 768 → List Bool) :=
  Function.update (Function.update high 175 []) 178 []

def finishHeadBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) : ℕ :=
  6*(Product.bytes right).length+6 +
    (Product.work p t M cache table u J left right []+2) +
    (6*(Product.bytes (Product.run p t M cache table u J left right [])).length+6) +
    (2*(Product.bytes right).length+3) + (2*(high 175).length+3) + (2*(high 178).length+3)

/-- A completed head is multiplied into the running product by the native
sparse-ring program, and both metadata tapes are physically cleared. -/
theorem finishHead_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool) (ht : high 164 = []) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ finishHeadBudget p t M cache table u J left right high, ∃ rr,
      Eval finishHead k (machine regs (Product.working e left [] right) high)
        (machine rr (Product.working e (Product.run p t M cache table u J left right []) [] [])
          (finishedHeadHigh high)) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let r1 := SubexponentialSAT.BitProgram.readRegs regs 0 1 none
  have h1 := move_core_eval regs (Product.working e left [] right)
    (Product.working e left right []) high 42 41 (by decide) ht (by
      funext i
      fin_cases i <;> simp [Product.working,Product.tapes,MomentsProgram.Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary])
  obtain ⟨np,hp,rp,h2⟩ := multiply_machine_eval p t M cache hz table degree width hd hw u J left right high r1
  let result := Product.run p t M cache table u J left right []
  let r3 := SubexponentialSAT.BitProgram.readRegs rp 0 1 none
  have h3 := move_core_eval rp (Product.working e [] right result)
    (Product.working e result right []) high 42 40 (by decide) ht (by
      funext i
      fin_cases i <;> simp [Product.working,Product.tapes,MomentsProgram.Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary])
  let r4 := SubexponentialSAT.BitProgram.readRegs r3 0 1 none
  have h4 := clear_right_eval r3 (Product.working e result right []) high
  let r5 := SubexponentialSAT.BitProgram.readRegs r4 0 1 none
  have h5 := clear_high_eval r4 (Product.working e result [] []) high 175 (by decide)
  have h6 := clear_high_eval r5 (Product.working e result [] []) (Function.update high 175 []) 178 (by decide)
  refine ⟨(6*(Product.bytes right).length+6)+(np+
    ((6*(Product.bytes result).length+6)+((2*(Product.bytes right).length+3)+
      ((2*(high 175).length+3)+(2*(high 178).length+3))))),?_,
      SubexponentialSAT.BitProgram.readRegs r5 0 1 none,?_⟩
  · dsimp [finishHeadBudget,result]
    omega
  · have h4' : Eval (clear 41) (2*(Product.bytes right).length+3)
        (machine r3 (Product.working e result right []) high)
        (machine r4 (Product.working e result [] []) high) := by
      simpa [emptyCore,Product.working,Product.bytes,MomentsProgram.Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary] using h4
    have h6' : Eval (clear 178) (2*(high 178).length+3)
        (machine r5 (Product.working e result [] []) (Function.update high 175 []))
        (machine (SubexponentialSAT.BitProgram.readRegs r5 0 1 none) (Product.working e result [] [])
          (finishedHeadHigh high)) := by simpa [finishedHeadHigh] using h6
    simpa [finishHead,corePorts,Product.tapes,emptyCore,Product.working,Product.bytes,
      MomentsProgram.Normalize.bytes, List.map_nil,List.flatten_nil,result,r1,r3,r4,r5]
      using h1.seq (h2.seq (h3.seq (h4'.seq (h5.seq h6'))))

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem assignmentStream_self (base : Fin 768 → List Bool) (bits : List Bool)
    (h160 : base 160 = bits) (h174 : base 174 = []) : assignmentStream base bits = base := by
  funext i
  by_cases h1 : i = 174
  · subst i; simp [assignmentStream,h174]
  by_cases h2 : i = 160
  · subst i; simp [assignmentStream,h160]
  simp [assignmentStream,h1,h2]

def afterHead (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool) :=
  finishedHeadHigh (assignmentStream (headHigh high h tail) [])

def headStepBudget (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool)
    (left : List (Product.Entry n (baseWidth p t) d)) :=
  headHeaderBudget h +
    (headWork p t M cache table meaning cost (headContext high h) left h.assignments []+1) +
    finishHeadBudget p t M cache table u J left
      (headRun p t M cache table meaning (headContext high h) h.assignments [])
      (assignmentStream (headHigh high h tail) [])

/-- A head record is decoded, its assignments are produced and added, and its
computed sum is multiplied into the current product. -/
theorem headStep_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (left : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool) (h : HeadInput) (tail : List Bool)
    (hsource : high 161 = Encoding.frame h.bits ++ tail)
    (h164 : high 164 = []) (h176 : high 176 = []) (h178 : high 178 = [])
    (h175 : high 175 = []) (h160 : high 160 = []) (h174 : high 174 = [])
    (hv : ∀ source x, validFrame
      (Function.update (Function.update (headHigh high h tail) 160 source) 174 x)) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ headStepBudget p t M cache table u J meaning cost high h tail left, ∃ rr,
      Eval (headStep produce) k (machine regs (Product.working e left [] []) high)
        (machine rr (Product.working e (headStepValue p t M cache table u J meaning high h left) [] [])
          (afterHead high h tail)) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let c := headContext high h
  let hh := headHigh high h tail
  obtain ⟨r1,h1⟩ := startHead_eval regs (Product.working e left [] []) high h tail
    hsource h164 h176 h178 h175 h160
  have hc : c.Matches hh := by
    simp [c,hh,headContext,AssignmentContext.Matches,headHigh,headHigh3,headHigh2,headHigh1]
  have ht : hh 164 = [] := by simp [hh,headHigh,headHigh3,headHigh2,headHigh1,h164]
  have hs : assignmentStream hh (rawFrames h.assignments) = hh :=
    assignmentStream_self hh _ (headHigh_assignments high h tail)
      (by simp [hh,headHigh,headHigh3,headHigh2,headHigh1,h174])
  obtain ⟨na,ha,r2,h2⟩ := assignmentScan_eval produce p t M cache hz table degree width hd hw
    u J meaning cost validFrame contract c hh hc ht hv h.assignments left [] r1
  rw [hs] at h2
  obtain ⟨nf,hf,r3,h3⟩ := finishHead_eval p t M cache hz table degree width hd hw u J left
    (headRun p t M cache table meaning c h.assignments []) (assignmentStream hh []) r2
    (by simp [assignmentStream,ht])
  refine ⟨headHeaderBudget h+(na+nf),?_,r3,?_⟩
  · dsimp [headStepBudget,c,hh] at *
    omega
  · simpa only [headStep,headStepValue,afterHead,c,hh,e] using h1.seq (h2.seq h3)

/-- Head-local metadata and temporary streams have no residue after the head. -/
theorem afterHead_eq (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool)
    (h176 : high 176 = []) (h178 : high 178 = []) (h175 : high 175 = [])
    (h160 : high 160 = []) (h174 : high 174 = []) :
    afterHead high h tail = Function.update high 161 tail := by
  funext i
  by_cases h1 : i = 160
  · subst i; simp [afterHead,finishedHeadHigh,assignmentStream,h160]
  by_cases h2 : i = 174
  · subst i; simp [afterHead,finishedHeadHigh,assignmentStream,h174]
  by_cases h3 : i = 175
  · subst i; simp [afterHead,finishedHeadHigh,h175]
  by_cases h4 : i = 178
  · subst i; simp [afterHead,finishedHeadHigh,h178]
  by_cases h5 : i = 176
  · subst i; simp [afterHead,finishedHeadHigh,assignmentStream,headHigh,h176]
  by_cases h6 : i = 161
  · subst i; simp [afterHead,finishedHeadHigh,assignmentStream,headHigh,headHigh3,headHigh2,headHigh1]
  simp [afterHead,finishedHeadHigh,assignmentStream,headHigh,headHigh3,headHigh2,headHigh1,h1,h2,h3,h4,h5,h6]

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem headHigh_update161 (base : Fin 768 → List Bool) (source : List Bool)
    (h : HeadInput) (tail : List Bool) :
    headHigh (Function.update base 161 source) h tail = headHigh base h tail := by
  simp [headHigh,headHigh3,headHigh2,headHigh1]

def headsWork (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (base : Fin 768 → List Bool) : List HeadInput → List (Product.Entry n (baseWidth p t) d) → ℕ
  | [], _ => 1
  | h::hs, left => headStepBudget p t M cache table u J meaning cost base h [] left + 2 +
      headsWork p t M cache table u J meaning cost base hs
        (headStepValue p t M cache table u J meaning base h left)

theorem headStepBudget_stream (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (base : Fin 768 → List Bool) (source tail : List Bool) (h : HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d)) :
    headStepBudget p t M cache table u J meaning cost (Function.update base 161 source) h tail left =
      headStepBudget p t M cache table u J meaning cost base h [] left := by
  simp [headStepBudget,headContext,finishHeadBudget,assignmentStream,
    headHigh,headHigh3,headHigh2,headHigh1]

/-- Actual iteration over all head records; the incoming accumulator is a
physical sparse dictionary, and each head is computed from its assignments. -/
theorem headLoop_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (base : Fin 768 → List Bool)
    (h164 : base 164 = []) (h176 : base 176 = []) (h178 : base 178 = [])
    (h175 : base 175 = []) (h160 : base 160 = []) (h174 : base 174 = [])
    (hs : List HeadInput)
    (hv : ∀ h ∈ hs, ∀ tail source x, validFrame
      (Function.update (Function.update (headHigh base h tail) 160 source) 174 x))
    (left : List (Product.Entry n (baseWidth p t) d)) (regs : Fin 40 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ headsWork p t M cache table u J meaning cost base hs left, ∃ rr,
      Eval (rawLoop 161 (headStep produce)) k
        (afterPeek (machine regs (Product.working e left [] [])
          (Function.update base 161 (rawFrames (hs.map HeadInput.bits)))) 161)
        (machine rr (Product.working e (headsRun p t M cache table u J meaning base hs left) [] [])
          (Function.update base 161 [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  induction hs generalizing left regs with
  | nil =>
      let a := machine regs (Product.working e left [] []) (Function.update base 161 [])
      have he : a.stacks 161 = [] := by simp [a,machine]
      refine ⟨1,le_rfl,(afterPeek a 161).regs,?_⟩
      simpa [headsRun,rawLoop,a,afterPeek,machine] using
        (Eval.while_false (body := .seq (headStep produce) (peek 161)) (peek_empty a 161 he))
  | cons h hs ih =>
      let source := rawFrames ((h::hs).map HeadInput.bits)
      let tail := rawFrames (hs.map HeadInput.bits)
      let high := Function.update base 161 source
      let a := machine regs (Product.working e left [] []) high
      let r0 := (afterPeek a 161).regs
      have ha : afterPeek a 161 = machine r0 (Product.working e left [] []) high := rfl
      obtain ⟨k,hk,r1,hh⟩ := headStep_eval produce p t M cache hz table degree width hd hw
        u J meaning cost validFrame contract left high r0 h tail
        (by simp [high,source,tail])
        (by simp [high,h164]) (by simp [high,h176]) (by simp [high,h178])
        (by simp [high,h175]) (by simp [high,h160]) (by simp [high,h174])
        (by simpa [high,headHigh_update161] using hv h (by simp) tail)
      let next := headStepValue p t M cache table u J meaning base h left
      have hfinished : afterHead high h tail = Function.update base 161 tail := by
        rw [afterHead_eq high h tail (by simp [high,h176]) (by simp [high,h178])
          (by simp [high,h175]) (by simp [high,h160]) (by simp [high,h174])]
        simp [high]
      have hh' : Eval (headStep produce) k (afterPeek a 161)
          (machine r1 (Product.working e next [] []) (Function.update base 161 tail)) := by
        simpa [ha,hfinished,headStepValue,headContext,high,next] using hh
      have hk' : k ≤ headStepBudget p t M cache table u J meaning cost base h [] left := by
        simpa [high,headStepBudget_stream] using hk
      obtain ⟨m,hm,rr,ht⟩ := ih (by intro h hh; exact hv h (by simp [hh])) next r1
      let b := machine r1 (Product.working e next [] []) (Function.update base 161 tail)
      have hne : a.stacks 161 ≠ [] := by
        simpa [a,high,machine,source] using rawFrames_cons_ne h.bits (hs.map HeadInput.bits)
      have he := Eval.while_true (peek_nonempty a 161 hne) (hh'.seq (peek_eval b 161)) ht
      refine ⟨k+1+m+1,?_,rr,?_⟩
      · simp only [headsWork]
        dsimp [next] at hm
        omega
      · simpa only [rawLoop,headsRun,next,a,b,tail,high,source] using he

theorem headScan_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (base : Fin 768 → List Bool)
    (h164 : base 164 = []) (h176 : base 176 = []) (h178 : base 178 = [])
    (h175 : base 175 = []) (h160 : base 160 = []) (h174 : base 174 = [])
    (hs : List HeadInput)
    (hv : ∀ h ∈ hs, ∀ tail source x, validFrame
      (Function.update (Function.update (headHigh base h tail) 160 source) 174 x))
    (left : List (Product.Entry n (baseWidth p t) d)) (regs : Fin 40 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ headsWork p t M cache table u J meaning cost base hs left+1, ∃ rr,
      Eval (headScan produce) k
        (machine regs (Product.working e left [] [])
          (Function.update base 161 (rawFrames (hs.map HeadInput.bits))))
        (machine rr (Product.working e (headsRun p t M cache table u J meaning base hs left) [] [])
          (Function.update base 161 [])) := by
  dsimp only
  obtain ⟨k,hk,rr,he⟩ := headLoop_eval produce p t M cache hz table degree width hd hw u J
    meaning cost validFrame contract base h164 h176 h178 h175 h160 h174 hs hv left regs
  exact ⟨1+k,by omega,rr,(peek_eval _ 161).seq he⟩

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open MomentsProgram

theorem copy_high_eval (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (src dst : Fin 768)
    (hs : 56 ≤ src.val) (hd : 56 ≤ dst.val)
    (hsd : src ≠ dst) (hst : src ≠ 179) (htd : (179 : Fin 768) ≠ dst)
    (ht : high 179 = []) :
    Eval (copy src dst) (7*(high src).length+5) (machine regs core high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) core
        (Function.update high dst (high src ++ high dst))) := by
  have he := copy_eval (machine regs core high) src dst hsd hst htd (by simpa [machine] using ht)
  convert he using 1
  · simp [machine,Nat.not_lt.mpr hs]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 56
      · have hid : i ≠ dst := by intro h; subst i; omega
        simp [machine,StackRoutines.copyStacks,hi,hid]
      · by_cases hid : i = dst
        · subst i
          simp [machine,StackRoutines.copyStacks,hi,Nat.not_lt.mpr hs]
        · simp [machine,StackRoutines.copyStacks,hi,hid]

theorem transfer_high_eval (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (src dst : Fin 768)
    (hs : 56 ≤ src.val) (hd : 56 ≤ dst.val) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(high src).length+3) (machine regs core high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) core
        (Function.update (Function.update high src []) dst ((high src).reverse ++ high dst))) := by
  have he := transfer_eval (machine regs core high) src dst hsd
  convert he using 1
  · simp [machine,Nat.not_lt.mpr hs]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 56
      · have his : i ≠ src := by intro h; subst i; omega
        have hid : i ≠ dst := by intro h; subst i; omega
        simp [machine,StackRoutines.transferStacks,hi,his,hid]
      · by_cases hid : i = dst
        · subst i
          simp [machine,StackRoutines.transferStacks,hi,Nat.not_lt.mpr hs]
        by_cases his : i = src
        · subst i
          simp [machine,StackRoutines.transferStacks,hi,hid]
        simp [machine,StackRoutines.transferStacks,hi,his,hid]

theorem move_high_core_eval (regs : Fin 40 → Bool) (a b : Product.Store)
    (high : Fin 768 → List Bool) (src : Fin 768) (dst : Fin 56)
    (hs : 56 ≤ src.val) (hst : src ≠ 164) (ht : high 164 = [])
    (hb : Product.tapes b = Function.update (Product.tapes a) dst (high src ++ Product.tapes a dst)) :
    Eval (moveForward src (corePorts dst)) (6*(high src).length+6) (machine regs a high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) b (Function.update high src [])) := by
  have hd : (164 : Fin 768) ≠ corePorts dst := by
    intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
  have hsd : src ≠ corePorts dst := by
    intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
  have he := moveForward_eval (machine regs a high) src (corePorts dst) hst hd hsd
    (by simpa [machine] using ht)
  convert he using 1
  · simp [machine,Nat.not_lt.mpr hs]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 56
      · let j : Fin 56 := ⟨i.val,hi⟩
        have hij : corePorts j = i := Fin.ext rfl
        have hjs : corePorts j ≠ src := by
          intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
        simp only [corePorts] at hjs
        rw [← hij]
        have hh := congrFun hb j
        simpa [machine,afterMove,corePorts,j.isLt,dst.isLt,Nat.not_lt.mpr hs,hjs,Function.update_apply,Fin.ext_iff] using hh
      · have hid : i ≠ corePorts dst := by intro h; subst i; exact hi dst.isLt
        by_cases his : i = src
        · subst i; simp [machine,hi,hid]
        · simp [machine,hi,hid,his]

theorem move_core_high_eval (regs : Fin 40 → Bool) (a b : Product.Store)
    (high : Fin 768 → List Bool) (src : Fin 56) (dst : Fin 768)
    (hd : 56 ≤ dst.val) (htd : (164 : Fin 768) ≠ dst) (ht : high 164 = [])
    (hb : Product.tapes b = Function.update (Product.tapes a) src []) :
    Eval (moveForward (corePorts src) dst) (6*(Product.tapes a src).length+6) (machine regs a high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) b
        (Function.update high dst (Product.tapes a src ++ high dst))) := by
  have hs : corePorts src ≠ 164 := by
    intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
  have hsd : corePorts src ≠ dst := by
    intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
  have he := moveForward_eval (machine regs a high) (corePorts src) dst hs htd hsd
    (by simpa [machine] using ht)
  convert he using 1
  · simp [machine_core]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 56
      · let j : Fin 56 := ⟨i.val,hi⟩
        have hij : corePorts j = i := Fin.ext rfl
        have hjd : corePorts j ≠ dst := by
          intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
        simp only [corePorts] at hjd
        rw [← hij]
        have hh := congrFun hb j
        simpa [machine,afterMove,corePorts,j.isLt,src.isLt,hjd,Function.update_apply,Fin.ext_iff] using hh
      · have his : i ≠ corePorts src := by intro h; subst i; exact hi src.isLt
        by_cases hid : i = dst
        · subst i
          simp [machine,hi,corePorts,src.isLt]
        · simp [machine,hi,hid,his]

theorem copy_high_core_eval (regs : Fin 40 → Bool) (a b : Product.Store)
    (high : Fin 768 → List Bool) (src : Fin 768) (dst : Fin 56)
    (hs : 56 ≤ src.val) (hst : src ≠ 179) (ht : high 179 = [])
    (hb : Product.tapes b = Function.update (Product.tapes a) dst (high src ++ Product.tapes a dst)) :
    Eval (copy src (corePorts dst)) (7*(high src).length+5) (machine regs a high)
      (machine (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) b high) := by
  have htd : (179 : Fin 768) ≠ corePorts dst := by
    intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
  have hsd : src ≠ corePorts dst := by
    intro h; have hv := congrArg Fin.val h; simp [corePorts] at hv; omega
  have he := copy_eval (machine regs a high) src (corePorts dst) hsd hst htd
    (by simpa [machine] using ht)
  convert he using 1
  · simp [machine,Nat.not_lt.mpr hs]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 56
      · let j : Fin 56 := ⟨i.val,hi⟩
        have hij : corePorts j = i := Fin.ext rfl
        rw [← hij]
        have hh := congrFun hb j
        simpa [machine,afterCopy,StackRoutines.copyStacks,corePorts,j.isLt,dst.isLt,Nat.not_lt.mpr hs,Function.update_apply,Fin.ext_iff] using hh
      · have hid : i ≠ corePorts dst := by intro h; subst i; exact hi dst.isLt
        simp [machine,StackRoutines.copyStacks,hi,hid]

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def projectionEntries {n B d : ℕ} (es : List (Product.Entry n B d)) :=
  es.map (fun a => MomentsProjectionProgram.ofIndex (a.1,RingProgram.flat a.2))

theorem projectionEntries_raw {n B d : ℕ} (es : List (Product.Entry n B d)) :
    MomentsProjectionProgram.raw (projectionEntries es) = Product.bytes es := by
  have h := MomentsProjectionProgram.raw_ofIndex
    (es.map (fun a => (a.1,RingProgram.flat a.2)))
  simpa [projectionEntries,Product.bytes,Normalize.bytes,List.map_map,Function.comp_def,
    Squarefree.Program.encodeDictionary] using h

theorem rawProject_flat {n B d : ℕ} (s : Finset (Fin n)) (es : List (Product.Entry n B d)) :
    Moments.rawProject s (es.map (fun a => (a.1,RingProgram.flat a.2))) =
      (Moments.rawProject s es).map (fun a => (a.1,RingProgram.flat a.2)) := by
  induction es with
  | nil => rfl
  | cons a es ih =>
      by_cases h : a.1.vars=s
      · simp [Moments.rawProject,h,ih]
      · simp [Moments.rawProject,h,ih]

theorem projectionEntries_selected {n B d : ℕ} (s : Finset (Fin n)) (es : List (Product.Entry n B d)) :
    MomentsProjectionProgram.selected (Squarefree.encodeMask s) (projectionEntries es) =
      projectionEntries (Moments.rawProject s es) := by
  have h := MomentsProjectionProgram.selected_ofIndex s
    (es.map (fun a => (a.1,RingProgram.flat a.2)))
  simpa [projectionEntries,rawProject_flat,List.map_map,Function.comp_def] using h

/-- Execute the exact-support projection with all unrelated arithmetic and
ambient tapes preserved. The encoded query was copied and reversed earlier. -/
theorem project_machine_eval {n B d : ℕ} (s : Finset (Fin n))
    (es : List (Product.Entry n B d)) (regs : Fin 40 → Bool)
    (core : Product.Store) (high : Fin 768 → List Bool)
    (hl : core.left = Product.bytes es)
    (hq : high 180 = (Squarefree.encodeMask s).reverse)
    (hw : ∀ i : Fin 768, 181 ≤ i.val → i.val ≤ 188 → high i = []) :
    ∃ k ≤ 200*((Product.bytes es).length+1)*(n+2)+1, ∃ rr,
      Eval project k (machine regs core high)
        (machine rr {core with left := []}
          (Function.update high 188 (Product.bytes (Moments.rawProject s es)))) := by
  let frame := machine regs core high
  let localRegs := regs ∘ projectionRegisters
  obtain ⟨k,hk,rr,he⟩ := project_eval (projectionEntries es) localRegs (Squarefree.encodeMask s) frame
  have h181 := hw 181 (by decide) (by decide)
  have h182 := hw 182 (by decide) (by decide)
  have h183 := hw 183 (by decide) (by decide)
  have h184 := hw 184 (by decide) (by decide)
  have h185 := hw 185 (by decide) (by decide)
  have h186 := hw 186 (by decide) (by decide)
  have h187 := hw 187 (by decide) (by decide)
  have h188 := hw 188 (by decide) (by decide)
  have ha : embedState projectionRegisters projectionPorts frame
      (MomentsProjectionProgram.machine localRegs
        (MomentsProjectionProgram.clean (MomentsProjectionProgram.raw (projectionEntries es))
          (Squarefree.encodeMask s) [])) = frame := by
    apply embedState_eq_of_ports _ _ _ _ _ projectionRegisters_injective projectionPorts_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [frame,machine,projectionPorts,MomentsProjectionProgram.machine,
        MomentsProjectionProgram.tapes,MomentsProjectionProgram.clean,Product.tapes,
        projectionEntries_raw,hl,hq,h181,h182,h183,h184,h185,h186,h187,h188]
    · intro i hi; rfl
  let result := Product.bytes (Moments.rawProject s es)
  let out : State 5 10 := MomentsProjectionProgram.machine rr
    {target := (Squarefree.encodeMask s).reverse, framed := result}
  let rf := (embedState projectionRegisters projectionPorts frame out).regs
  have hb : embedState projectionRegisters projectionPorts frame out =
      machine rf {core with left := []} (Function.update high 188 result) := by
    apply embedState_eq_of_ports _ _ _ _ _ projectionRegisters_injective projectionPorts_injective
    · intro i; exact embedState_register projectionRegisters projectionPorts frame out projectionRegisters_injective i
    · intro i hi; exact embedState_register_frame projectionRegisters projectionPorts frame out i hi
    · intro i
      fin_cases i <;> simp [machine,projectionPorts,out,MomentsProjectionProgram.machine,
        MomentsProjectionProgram.tapes,Product.tapes,hq,h181,h182,h183,h184,h185,h186,h187]
    · intro i hi
      have h40 : i ≠ 40 := by
        intro h; apply hi; exact ⟨0,by simpa [projectionPorts] using h.symm⟩
      have h188' : i ≠ 188 := by
        intro h; apply hi; exact ⟨9,by simpa [projectionPorts] using h.symm⟩
      by_cases hil : i.val < 56
      · have hj : (⟨i.val,hil⟩ : Fin 56) ≠ 40 := by
          intro h
          apply h40
          apply Fin.ext
          have hh := congrArg (fun x : Fin 56 => x.val) h
          exact hh
        simp [machine,frame,hil,Product.tapes,hj]
      · simp [machine,frame,hil,h188']
  refine ⟨k,?_,rf,?_⟩
  · simpa [projectionEntries_raw,Squarefree.encodeMask] using hk
  · rw [ha] at he
    have he' : Eval project k frame (embedState projectionRegisters projectionPorts frame out) := by
      simpa only [out,result,projectionEntries_selected,projectionEntries_raw] using he
    simpa only [hb] using he'

/-- Native normalization adds projected records into the actual current
answer dictionary, using the ordinary runtime degree and modulus caches. -/
theorem normalize_machine_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (source seed : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ 9*(Product.bytes source).length+9*d+
      Normalize.work p t M cache Squarefree.encodeIndex source seed+19, ∃ rr,
      Eval normalize k
        (machine regs {Product.working e [] [] seed with mapped := Product.bytes source} high)
        (machine rr (Product.working e [] [] (Normalize.run p t M cache source seed)) high) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let a := {Product.working e ([] : List (Product.Entry n (baseWidth p t) d)) [] seed
    with mapped := Product.bytes source}
  obtain ⟨k,hk,rr,he⟩ := Product.normalizePhase_eval p t M cache Squarefree.encodeIndex
    Squarefree.encodeIndex_injective source seed (regs ∘ coreRegisters) a rfl hw hd
    rfl rfl rfl rfl rfl rfl rfl rfl
  have hl := eval_liftCommand he 4 42 coreRegisters corePorts (machine regs a high)
    coreRegisters_injective corePorts_injective
  refine ⟨k+1,?_,combineRegisters regs rr,?_⟩
  · dsimp [a,Product.working,e,Product.environment,Product.idle] at hk
    rw [hd] at hk
    omega
  · simpa [normalize,← coreState.eq_1,coreState_machine,combineRegisters_self,a,
      Product.working,e,Product.environment,Product.idle] using hl

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def supportOutput (high : Fin 768 → List Bool) (result : List Bool) :=
  Function.update (Function.update high 166 result) 168 []

def finishSupportBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d)) : ℕ :=
  let projected := Moments.rawProject s product
  let result := supportValue p t M cache s product seed
  200*((Product.bytes product).length+1)*(n+2)+14*n+
    15*(Product.bytes projected).length+6*(Product.bytes seed).length+
    6*(Product.bytes result).length+9*d+
    Normalize.work p t M cache Squarefree.encodeIndex projected seed+60

/-- The support finish phase copies its mask, projects the computed head
product, adds into the actual accumulated answer, and restores all scratch. -/
theorem finishSupport_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hmask : high 168 = Squarefree.encodeMask s) (hseed : high 166 = Product.bytes seed)
    (h164 : high 164 = []) (h179 : high 179 = [])
    (hwork : ∀ i : Fin 768, 180 ≤ i.val → i.val ≤ 188 → high i = []) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ finishSupportBudget p t M cache s product seed, ∃ rr,
      Eval finishSupport k (machine regs (Product.working e product [] []) high)
        (machine rr (emptyCore e)
          (supportOutput high (Product.bytes (supportValue p t M cache s product seed)))) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let projected := Moments.rawProject s product
  let result := supportValue p t M cache s product seed
  let mask := Squarefree.encodeMask s
  have hmasklen : mask.length=n := by simp [mask,Squarefree.encodeMask]
  have h180 := hwork 180 (by decide) (by decide)
  have h188 := hwork 188 (by decide) (by decide)
  let r1 := SubexponentialSAT.BitProgram.readRegs regs 0 1 none
  let high1 := Function.update high 164 mask
  have h1 := copy_high_eval regs (Product.working e product [] []) high 168 164
    (by decide) (by decide) (by decide) (by decide) (by decide) h179
  have h1' : Eval (copy 168 164) (7*n+5) (machine regs (Product.working e product [] []) high)
      (machine r1 (Product.working e product [] []) high1) := by
    simpa [hmask,h164,high1,mask,hmasklen] using h1
  let r2 := SubexponentialSAT.BitProgram.readRegs r1 0 1 none
  let high2 := Function.update (Function.update high1 164 []) 180 mask.reverse
  have h2 := transfer_high_eval r1 (Product.working e product [] []) high1 164 180
    (by decide) (by decide) (by decide)
  have h2' : Eval (transfer 164 180) (3*n+3)
      (machine r1 (Product.working e product [] []) high1)
      (machine r2 (Product.working e product [] []) high2) := by
    simpa [high1,high2,h180,hmasklen] using h2
  obtain ⟨np,hp,r3,h3⟩ := project_machine_eval s product r2 (Product.working e product [] []) high2
    rfl (by simp [high2,mask]) (by
      intro i hi hj
      have hne180 : i ≠ 180 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      have hne164 : i ≠ 164 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      simpa [high2,high1,hne180,hne164] using hwork i (by omega) hj)
  let high3 := Function.update high2 188 (Product.bytes projected)
  have h3' : Eval project np (machine r2 (Product.working e product [] []) high2)
      (machine r3 (emptyCore e) high3) := by
    simpa [emptyCore,Product.working,Product.bytes,Normalize.bytes,high3,projected,
      Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary] using h3
  let core4 := {Product.working e ([] : List (Product.Entry n (baseWidth p t) d)) [] []
    with mapped := Product.bytes projected}
  let high4 := Function.update high3 188 []
  let r4 := SubexponentialSAT.BitProgram.readRegs r3 0 1 none
  have h4 := move_high_core_eval r3 (emptyCore e) core4 high3 188 4
    (by decide) (by decide) (by simp [high3,high2,high1]) (by
      funext i; fin_cases i <;> simp [core4,high3,Product.tapes,emptyCore,emptyCore,Product.working,e,
        Product.environment,Product.idle,Product.bytes,Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary])
  let core5 := {Product.working e ([] : List (Product.Entry n (baseWidth p t) d)) [] seed
    with mapped := Product.bytes projected}
  let high5 := Function.update high4 166 []
  let r5 := SubexponentialSAT.BitProgram.readRegs r4 0 1 none
  have h5 := move_high_core_eval r4 core4 core5 high4 166 42
    (by decide) (by decide) (by simp [high4,high3,high2,high1]) (by
      funext i; fin_cases i <;> simp [core5,core4,high4,high3,high2,high1,hseed,
        Product.tapes,Product.working,e,Product.environment,Product.idle,Product.bytes,Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary])
  obtain ⟨nn,hn,r6,h6⟩ := normalize_machine_eval p t M cache table degree width hd hw u J
    projected seed high5 r5
  let high7 := Function.update high5 166 (Product.bytes result)
  let r7 := SubexponentialSAT.BitProgram.readRegs r6 0 1 none
  have h7 := move_core_high_eval r6 (Product.working e [] [] result)
    (emptyCore e) high5 42 166 (by decide) (by decide)
    (by simp [high5,high4,high3,high2,high1]) (by
      funext i; fin_cases i <;> simp [Product.tapes,emptyCore,Product.working,Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary])
  let high8 := Function.update high7 180 []
  let r8 := SubexponentialSAT.BitProgram.readRegs r7 0 1 none
  have h8 := clear_high_eval r7 (emptyCore e) high7 180 (by decide)
  have h9 := clear_high_eval r8 (emptyCore e) high8 168 (by decide)
  have hout : Function.update high8 168 [] = supportOutput high (Product.bytes result) := by
    funext i
    by_cases ha : i = 168
    · subst i; simp [supportOutput]
    by_cases hb : i = 166
    · subst i; simp [high8,high7,supportOutput]
    by_cases hc : i = 180
    · subst i; simp [high8,supportOutput,h180]
    by_cases he : i = 188
    · subst i; simp [high8,high7,high5,high4,supportOutput,h188]
    by_cases hf : i = 164
    · subst i; simp [high8,high7,high5,high4,high3,high2,supportOutput,h164]
    simp [high8,high7,high5,high4,high3,high2,high1,supportOutput,ha,hb,hc,he,hf]
  refine ⟨(7*n+5)+((3*n+3)+(np+
      ((6*(Product.bytes projected).length+6)+((6*(Product.bytes seed).length+6)+
        (nn+((6*(Product.bytes result).length+6)+((2*n+3)+(2*n+3)))))))),?_,
      SubexponentialSAT.BitProgram.readRegs r8 0 1 none,?_⟩
  · dsimp [finishSupportBudget,projected,result] at *
    omega
  · have h4' : Eval (moveForward 188 4) (6*(Product.bytes projected).length+6)
        (machine r3 (emptyCore e) high3) (machine r4 core4 high4) := by
      simpa [corePorts,high3,high4] using h4
    have h5' : Eval (moveForward 166 42) (6*(Product.bytes seed).length+6)
        (machine r4 core4 high4) (machine r5 core5 high5) := by
      simpa [corePorts,high5,high4,high3,high2,high1,hseed] using h5
    have h7' : Eval (moveForward 42 166) (6*(Product.bytes result).length+6)
        (machine r6 (Product.working e [] [] result) high5)
        (machine r7 (emptyCore e) high7) := by
      simpa [corePorts,Product.tapes,emptyCore,Product.working,high7,high5] using h7
    have h8' : Eval (clear 180) (2*n+3)
        (machine r7 (emptyCore e) high7)
        (machine r8 (emptyCore e) high8) := by
      simpa [high8,high7,high5,high4,high3,high2,hmasklen] using h8
    have h9' : Eval (clear 168) (2*n+3)
        (machine r8 (emptyCore e) high8)
        (machine (SubexponentialSAT.BitProgram.readRegs r8 0 1 none) (emptyCore e)
          (supportOutput high (Product.bytes result))) := by
      rw [hout] at h9
      simpa [high8,high7,high5,high4,high3,high2,high1,hmask,mask,hmasklen] using h9
    simpa only [finishSupport,core5,result,supportValue] using
      h1'.seq (h2'.seq (h3'.seq (h4'.seq (h5'.seq (h6.seq (h7'.seq (h8'.seq h9')))))))

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open MomentsProgram

def supportHigh (high : Fin 768 → List Bool) (mask tail : List Bool) :=
  Function.update (Function.update (Function.update high 162 tail) 168 mask) 161 (high 170)

theorem startSupport_eval {n B d : ℕ} (one : List (Product.Entry n B d))
    (e : Product.Store) (regs : Fin 40 → Bool) (high : Fin 768 → List Bool)
    (mask tail : List Bool) (hsrc : high 162 = Encoding.frame mask ++ tail)
    (h164 : high 164 = []) (h168 : high 168 = []) (h179 : high 179 = [])
    (h161 : high 161 = []) (hone : high 167 = Product.bytes one) :
    ∃ rr, Eval startSupport
      (9*mask.length+7+7*(Product.bytes one).length+5+7*(high 170).length+5)
      (machine regs (emptyCore e) high)
      (machine rr (Product.working e one [] []) (supportHigh high mask tail)) := by
  let r1 := SubexponentialSAT.BitProgram.readRegs regs 0 1 none
  let high1 := Function.update (Function.update high 162 tail) 168 mask
  have h1 := takeFrame_eval (machine regs (emptyCore e) high) 162 168
    (by decide) (by decide) (by decide) mask tail (by simpa [machine] using hsrc)
    (by simpa [machine] using h164) (by simpa [machine] using h168)
  rw [afterTake_machine regs (emptyCore e) high 162 168 (by decide) (by decide)] at h1
  let r2 := SubexponentialSAT.BitProgram.readRegs r1 0 1 none
  have h2 := copy_high_core_eval r1 (emptyCore e) (Product.working e one [] [])
    high1 167 40 (by decide) (by decide) (by simp [high1,h179]) (by
      funext i
      fin_cases i <;> simp [high1,hone,emptyCore,Product.working,Product.tapes,Product.bytes,Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary])
  have h3 := copy_high_eval r2 (Product.working e one [] []) high1 170 161
    (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [high1,h179])
  refine ⟨SubexponentialSAT.BitProgram.readRegs r2 0 1 none,?_⟩
  have h1' : Eval (takeFrame 162 168 (by decide)) (9*mask.length+7)
      (machine regs (emptyCore e) high)
      (machine r1 (emptyCore e) high1) := h1
  have h2' : Eval (copy 167 40) (7*(Product.bytes one).length+5)
      (machine r1 (emptyCore e) high1)
      (machine r2 (Product.working e one [] []) high1) := by
    simpa [high1,hone,corePorts] using h2
  have h3' : Eval (copy 170 161) (7*(high 170).length+5)
      (machine r2 (Product.working e one [] []) high1)
      (machine (SubexponentialSAT.BitProgram.readRegs r2 0 1 none) (Product.working e one [] [])
        (supportHigh high mask tail)) := by
    simpa [supportHigh,high1,h161] using h3
  simpa only [startSupport, Nat.add_assoc] using h1'.seq (h2'.seq h3')

def bucketHigh1 (high : Fin 768 → List Bool) (b : BucketInput) (tail : List Bool) :=
  Function.update (Function.update high 163 tail) 176 b.bits
def bucketHigh2 (high : Fin 768 → List Bool) (b : BucketInput) (tail : List Bool) :=
  Function.update (Function.update (bucketHigh1 high b tail) 176
    (Encoding.frame (rawFrames (b.heads.map HeadInput.bits)))) 177 b.context
def bucketHigh3 (high : Fin 768 → List Bool) (b : BucketInput) (tail : List Bool) :=
  Function.update (Function.update (bucketHigh2 high b tail) 176 [])
    170 (rawFrames (b.heads.map HeadInput.bits))
def bucketHigh (high : Fin 768 → List Bool) (b : BucketInput) (tail : List Bool) :=
  Function.update (bucketHigh3 high b tail) 162 (high 169)

def bucketHeaderBudget (high : Fin 768 → List Bool) (b : BucketInput) : ℕ :=
  9*(b.bits.length+b.context.length+(rawFrames (b.heads.map HeadInput.bits)).length)+
    7*(high 169).length+26

/-- Decode a real bucket tuple, retain its head list as a master, and copy
its reusable support list by native list movement. -/
theorem startBucket_eval (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) (b : BucketInput) (tail : List Bool)
    (hsrc : high 163 = Encoding.frame b.bits ++ tail)
    (h164 : high 164 = []) (h176 : high 176 = []) (h177 : high 177 = [])
    (h170 : high 170 = []) (h162 : high 162 = []) (h179 : high 179 = []) :
    ∃ rr, Eval startBucket (bucketHeaderBudget high b)
      (machine regs core high) (machine rr core (bucketHigh high b tail)) := by
  let r1 := SubexponentialSAT.BitProgram.readRegs regs 0 1 none
  let r2 := SubexponentialSAT.BitProgram.readRegs r1 0 1 none
  let r3 := SubexponentialSAT.BitProgram.readRegs r2 0 1 none
  have h1 := takeFrame_eval (machine regs core high) 163 176 (by decide) (by decide) (by decide)
    b.bits tail (by simpa [machine] using hsrc) (by simpa [machine] using h164)
    (by simpa [machine] using h176)
  rw [afterTake_machine regs core high 163 176 (by decide) (by decide)] at h1
  have h1' : Eval (takeFrame 163 176 (by decide)) (9*b.bits.length+7)
      (machine regs core high) (machine r1 core (bucketHigh1 high b tail)) := h1
  have h2 := takeFrame_eval (machine r1 core (bucketHigh1 high b tail)) 176 177
    (by decide) (by decide) (by decide) b.context (Encoding.frame (rawFrames (b.heads.map HeadInput.bits)))
    (by simp [machine,bucketHigh1,BucketInput.bits])
    (by simp [machine,bucketHigh1,h164]) (by simp [machine,bucketHigh1,h177])
  rw [afterTake_machine r1 core (bucketHigh1 high b tail) 176 177 (by decide) (by decide)] at h2
  have h2' : Eval (takeFrame 176 177 (by decide)) (9*b.context.length+7)
      (machine r1 core (bucketHigh1 high b tail)) (machine r2 core (bucketHigh2 high b tail)) := h2
  have h3 := takeFrame_eval (machine r2 core (bucketHigh2 high b tail)) 176 170
    (by decide) (by decide) (by decide) (rawFrames (b.heads.map HeadInput.bits)) []
    (by simp [machine,bucketHigh2]) (by simp [machine,bucketHigh2,bucketHigh1,h164])
    (by simp [machine,bucketHigh2,bucketHigh1,h170])
  rw [afterTake_machine r2 core (bucketHigh2 high b tail) 176 170 (by decide) (by decide)] at h3
  have h3' : Eval (takeFrame 176 170 (by decide)) (9*(rawFrames (b.heads.map HeadInput.bits)).length+7)
      (machine r2 core (bucketHigh2 high b tail)) (machine r3 core (bucketHigh3 high b tail)) := h3
  have h4 := copy_high_eval r3 core (bucketHigh3 high b tail) 169 162
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [bucketHigh3,bucketHigh2,bucketHigh1,h179])
  have h4' : Eval (copy 169 162) (7*(high 169).length+5)
      (machine r3 core (bucketHigh3 high b tail))
      (machine (SubexponentialSAT.BitProgram.readRegs r3 0 1 none) core (bucketHigh high b tail)) := by
    simpa [bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,h162] using h4
  refine ⟨SubexponentialSAT.BitProgram.readRegs r3 0 1 none,?_⟩
  convert h1'.seq (h2'.seq (h3'.seq h4')) using 1 <;>
    first | rfl | (unfold bucketHeaderBudget; omega)

theorem finishBucket_eval (regs : Fin 40 → Bool) (core : Product.Store)
    (high : Fin 768 → List Bool) :
    ∃ rr, Eval finishBucket (2*(high 177).length+3+(2*(high 170).length+3))
      (machine regs core high)
      (machine rr core (Function.update (Function.update high 177 []) 170 [])) := by
  have h1 := clear_high_eval regs core high 177 (by decide)
  have h2 := clear_high_eval (SubexponentialSAT.BitProgram.readRegs regs 0 1 none) core
    (Function.update high 177 []) 170 (by decide)
  exact ⟨_,by simpa [finishBucket] using h1.seq h2⟩

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem headContext_congr (a b : Fin 768 → List Bool) (h : HeadInput)
    (h168 : a 168 = b 168) (h177 : a 177 = b 177) : headContext a h = headContext b h := by
  simp [headContext,h168,h177]

theorem headStepValue_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (a b : Fin 768 → List Bool) (h168 : a 168 = b 168) (h177 : a 177 = b 177)
    (h : HeadInput) (left : List (Product.Entry n (baseWidth p t) d)) :
    headStepValue p t M cache table u J meaning a h left =
      headStepValue p t M cache table u J meaning b h left := by
  simp only [headStepValue,headContext_congr a b h h168 h177]

theorem headsRun_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (a b : Fin 768 → List Bool) (h168 : a 168 = b 168) (h177 : a 177 = b 177)
    (hs : List HeadInput) (left : List (Product.Entry n (baseWidth p t) d)) :
    headsRun p t M cache table u J meaning a hs left =
      headsRun p t M cache table u J meaning b hs left := by
  induction hs generalizing left with
  | nil => rfl
  | cons h hs ih =>
      simp only [headsRun,headStepValue_congr p t M cache table u J meaning a b h168 h177,ih]

def supportFinished (high : Fin 768 → List Bool) (tail result : List Bool) :=
  Function.update (Function.update high 162 tail) 166 result

def supportStepBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (high : Fin 768 → List Bool) (hs : List HeadInput) (tail : List Bool)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n)) :=
  9*n+7+7*(Product.bytes one).length+5+7*(high 170).length+5 +
    (headsWork p t M cache table u J meaning cost (supportHigh high (Squarefree.encodeMask s) tail) hs one+1) +
    finishSupportBudget p t M cache s (supportProduct p t M cache table u J meaning high hs one s) seed

/-- One support is read from the actual support stream, every head is
computed, and the projected product is added to the actual answer tape. -/
theorem supportStep_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n))
    (hs : List HeadInput) (tail : List Bool) (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hsrc : high 162 = Encoding.frame (Squarefree.encodeMask s) ++ tail)
    (hheads : high 170 = rawFrames (hs.map HeadInput.bits))
    (hone : high 167 = Product.bytes one) (hseed : high 166 = Product.bytes seed)
    (h160 : high 160 = []) (h161 : high 161 = []) (h164 : high 164 = []) (h168 : high 168 = [])
    (h174 : high 174 = []) (h175 : high 175 = []) (h176 : high 176 = []) (h178 : high 178 = [])
    (h179 : high 179 = [])
    (hwork : ∀ i : Fin 768, 180 ≤ i.val → i.val ≤ 188 → high i = [])
    (hv : ∀ h ∈ hs, ∀ headTail source x, validFrame
      (Function.update (Function.update
        (headHigh (supportHigh high (Squarefree.encodeMask s) tail) h headTail) 160 source) 174 x)) :
    let e := Product.environment p t M cache table degree width u J
    let result := supportValue p t M cache s (supportProduct p t M cache table u J meaning high hs one s) seed
    ∃ k ≤ supportStepBudget p t M cache table u J meaning cost high hs tail one seed s, ∃ rr,
      Eval (supportStep produce) k (machine regs (emptyCore e) high)
        (machine rr (emptyCore e) (supportFinished high tail (Product.bytes result))) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let base := supportHigh high (Squarefree.encodeMask s) tail
  obtain ⟨r1,h1⟩ := startSupport_eval one e regs high (Squarefree.encodeMask s) tail
    hsrc h164 h168 h179 h161 hone
  obtain ⟨nh,hh,r2,h2⟩ := headScan_eval produce p t M cache hz table degree width hd hw u J
    meaning cost validFrame contract base
    (by simp [base,supportHigh,h164]) (by simp [base,supportHigh,h176])
    (by simp [base,supportHigh,h178]) (by simp [base,supportHigh,h175])
    (by simp [base,supportHigh,h160]) (by simp [base,supportHigh,h174]) hs hv one r1
  have hbase : Function.update base 161 (rawFrames (hs.map HeadInput.bits)) = base := by
    funext i
    by_cases hi : i = 161
    · subst i; simp [base,supportHigh,hheads]
    · simp [hi]
  rw [hbase] at h2
  have hp : headsRun p t M cache table u J meaning base hs one =
      supportProduct p t M cache table u J meaning high hs one s := by
    apply headsRun_congr p t M cache table u J meaning base
      (Function.update high 168 (Squarefree.encodeMask s))
    · simp [base,supportHigh]
    · simp [base,supportHigh]
  rw [hp] at h2
  let afterHeads := Function.update base 161 []
  obtain ⟨nf,hf,r3,h3⟩ := finishSupport_eval p t M cache table degree width hd hw u J s
    (supportProduct p t M cache table u J meaning high hs one s) seed afterHeads r2
    (by simp [afterHeads,base,supportHigh]) (by simp [afterHeads,base,supportHigh,hseed])
    (by simp [afterHeads,base,supportHigh,h164]) (by simp [afterHeads,base,supportHigh,h179]) (by
      intro i hi hj
      have h1 : i ≠ 161 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      have h2 : i ≠ 168 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      have h3 : i ≠ 162 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
      simpa [afterHeads,base,supportHigh,h1,h2,h3] using hwork i hi hj)
  let result := supportValue p t M cache s (supportProduct p t M cache table u J meaning high hs one s) seed
  have hout : supportOutput afterHeads (Product.bytes result) = supportFinished high tail (Product.bytes result) := by
    funext i
    by_cases ha : i = 166
    · subst i; simp [supportOutput,supportFinished]
    by_cases hb : i = 168
    · subst i; simp [supportOutput,supportFinished,h168]
    by_cases hc : i = 161
    · subst i; simp [supportOutput,supportFinished,afterHeads,h161]
    by_cases he : i = 162
    · subst i; simp [supportOutput,supportFinished,afterHeads,base,supportHigh]
    simp [supportOutput,supportFinished,afterHeads,base,supportHigh,ha,hb,hc,he]
  refine ⟨(9*n+7+7*(Product.bytes one).length+5+7*(high 170).length+5)+(nh+nf),?_,r3,?_⟩
  · dsimp [supportStepBudget,base] at *
    omega
  · rw [hout] at h3
    simpa only [supportStep,Squarefree.encodeMask,List.length_ofFn,base,afterHeads,result]
      using h1.seq (h2.seq h3)

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def supportStream (base : Fin 768 → List Bool) (seed source : List Bool) :=
  Function.update (Function.update base 162 source) 166 seed

theorem supportFinished_stream (base : Fin 768 → List Bool) (seed source tail result : List Bool) :
    supportFinished (supportStream base seed source) tail result = supportStream base result tail := by
  funext i
  by_cases h1 : i=166
  · subst i; simp [supportFinished,supportStream]
  by_cases h2 : i=162
  · subst i; simp [supportFinished,supportStream]
  simp [supportFinished,supportStream,h1,h2]

theorem headStepBudget_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (a b : Fin 768 → List Bool) (h168 : a 168 = b 168) (h177 : a 177 = b 177)
    (h : HeadInput) (ta tb : List Bool) (left : List (Product.Entry n (baseWidth p t) d)) :
    headStepBudget p t M cache table u J meaning cost a h ta left =
      headStepBudget p t M cache table u J meaning cost b h tb left := by
  simp [headStepBudget,finishHeadBudget,assignmentStream,headHigh,headHigh3,
    headHigh2,headHigh1,headContext,h168,h177]

theorem headsWork_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (a b : Fin 768 → List Bool) (h168 : a 168 = b 168) (h177 : a 177 = b 177)
    (hs : List HeadInput) (left : List (Product.Entry n (baseWidth p t) d)) :
    headsWork p t M cache table u J meaning cost a hs left =
      headsWork p t M cache table u J meaning cost b hs left := by
  induction hs generalizing left with
  | nil => rfl
  | cons h hs ih =>
      simp only [headsWork,headStepBudget_congr p t M cache table u J meaning cost a b h168 h177 h [] [] left,
        headStepValue_congr p t M cache table u J meaning a b h168 h177,ih]

theorem supportProduct_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (a b : Fin 768 → List Bool) (h177 : a 177 = b 177)
    (hs : List HeadInput) (one : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n)) :
    supportProduct p t M cache table u J meaning a hs one s =
      supportProduct p t M cache table u J meaning b hs one s := by
  apply headsRun_congr p t M cache table u J meaning
  · simp
  · simpa using h177

theorem supportStepBudget_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (a b : Fin 768 → List Bool) (h170 : a 170 = b 170) (h177 : a 177 = b 177)
    (hs : List HeadInput) (ta tb : List Bool)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n)) :
    supportStepBudget p t M cache table u J meaning cost a hs ta one seed s =
      supportStepBudget p t M cache table u J meaning cost b hs tb one seed s := by
  have hw := headsWork_congr p t M cache table u J meaning cost
    (supportHigh a (Squarefree.encodeMask s) ta) (supportHigh b (Squarefree.encodeMask s) tb)
    (by simp [supportHigh]) (by simpa [supportHigh] using h177) hs one
  simp only [supportStepBudget,h170,hw,supportProduct_congr p t M cache table u J meaning a b h177]

theorem supportsRun_foldl (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (base : Fin 768 → List Bool) (hs : List HeadInput) (one : List (Product.Entry n (baseWidth p t) d))
    (ss : List (Finset (Fin n))) (seed : List (Product.Entry n (baseWidth p t) d)) :
    ss.foldl (fun a s => supportValue p t M cache s
      (supportProduct p t M cache table u J meaning base hs one s) a) seed =
      supportsRun p t M cache table u J meaning base hs one ss seed := by
  induction ss generalizing seed with
  | nil => rfl
  | cons s ss ih => simpa only [List.foldl,supportsRun] using ih (supportValue p t M cache s (supportProduct p t M cache table u J meaning base hs one s) seed)

def supportsWork (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (base : Fin 768 → List Bool) (hs : List HeadInput) (one : List (Product.Entry n (baseWidth p t) d))
    (ss : List (Finset (Fin n))) (seed : List (Product.Entry n (baseWidth p t) d)) :=
  scanWork (fun a s => supportStepBudget p t M cache table u J meaning cost base hs [] one a s)
    (fun a s => supportValue p t M cache s (supportProduct p t M cache table u J meaning base hs one s) a)
    seed ss+1

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def SupportClean (high : Fin 768 → List Bool) : Prop :=
  ∀ i : Fin 768, i ∈ ([160,161,164,168,174,175,176,178,179] : List (Fin 768)) ∨
    (180 ≤ i.val ∧ i.val ≤ 188) → high i = []

def SupportFrames {n : ℕ} (valid : (Fin 768 → List Bool) → Prop)
    (base : Fin 768 → List Bool) (hs : List HeadInput) : Prop :=
  ∀ (s : Finset (Fin n)) seed source tail h, h ∈ hs → ∀ headTail assignments x,
    valid (Function.update (Function.update
      (headHigh (supportHigh (supportStream base seed source) (Squarefree.encodeMask s) tail)
        h headTail) 160 assignments) 174 x)

/-- The actual support while-loop. The cost is the sum of all physical
support steps, including all nested assignment and head loops. -/
theorem supportScan_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (hs : List HeadInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hheads : base 170 = rawFrames (hs.map HeadInput.bits)) (hone : base 167 = Product.bytes one)
    (hclean : SupportClean base) (hv : SupportFrames (n:=n) validFrame base hs) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ supportsWork p t M cache table u J meaning cost base hs one ss seed, ∃ rr,
      Eval (supportScan produce) k
        (machine regs (emptyCore e)
          (supportStream base (Product.bytes seed) (rawFrames (ss.map Squarefree.encodeMask))))
        (machine rr (emptyCore e)
          (supportStream base (Product.bytes (supportsRun p t M cache table u J meaning base hs one ss seed)) [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let next := fun (a : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n)) =>
    supportValue p t M cache s (supportProduct p t M cache table u J meaning base hs one s) a
  let budget := fun (a : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n)) =>
    supportStepBudget p t M cache table u J meaning cost base hs [] one a s
  let inv := fun (a : List (Product.Entry n (baseWidth p t) d)) (tapes : Fin 768 → List Bool) =>
    ∃ source, tapes = (machine (fun _ => false) (emptyCore e)
      (supportStream base (Product.bytes a) source)).stacks
  have body : BodyContract 162 (supportStep produce) Squarefree.encodeMask next budget inv := by
    intro a s tail state hi hsrc
    obtain ⟨source,htapes⟩ := hi
    have hsource : source = Encoding.frame (Squarefree.encodeMask s) ++ tail := by
      have he := (congrFun htapes 162).symm.trans hsrc
      simpa [machine,supportStream] using he
    subst source
    let high := supportStream base (Product.bytes a) (Encoding.frame (Squarefree.encodeMask s) ++ tail)
    have heq : state = machine state.regs (emptyCore e) high := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · exact htapes
    have hc : SupportClean high := by
      intro i hi
      have hn162 : i ≠ 162 := by
        intro he; subst i; norm_num [Fin.ext_iff] at hi
      have hn166 : i ≠ 166 := by
        intro he; subst i; norm_num [Fin.ext_iff] at hi
      simpa [high,supportStream,hn162,hn166] using hclean i hi
    obtain ⟨k,hk,rr,he⟩ := supportStep_eval produce p t M cache hz table degree width hd hw u J
      meaning cost validFrame contract one a s hs tail high state.regs
      (by simp [high,supportStream]) (by simpa [high,supportStream] using hheads)
      (by simpa [high,supportStream] using hone) (by simp [high,supportStream])
      (hc 160 (Or.inl (by decide))) (hc 161 (Or.inl (by decide)))
      (hc 164 (Or.inl (by decide))) (hc 168 (Or.inl (by decide)))
      (hc 174 (Or.inl (by decide))) (hc 175 (Or.inl (by decide)))
      (hc 176 (Or.inl (by decide))) (hc 178 (Or.inl (by decide)))
      (hc 179 (Or.inl (by decide))) (fun i hi hj => hc i (Or.inr ⟨hi,hj⟩))
      (by intro h hh; exact hv s (Product.bytes a) _ tail h hh)
    have hvprod : supportProduct p t M cache table u J meaning high hs one s =
        supportProduct p t M cache table u J meaning base hs one s :=
      supportProduct_congr p t M cache table u J meaning high base (by simp [high,supportStream]) hs one s
    have hbound : k ≤ budget a s := by
      simpa only [budget,supportStepBudget_congr p t M cache table u J meaning cost high base
        (by simp [high,supportStream]) (by simp [high,supportStream]) hs tail [] one a s] using hk
    let out := machine rr (emptyCore e) (supportStream base (Product.bytes (next a s)) tail)
    refine ⟨k,hbound,out,⟨tail,rfl⟩,?_,?_⟩
    · simp [out,machine,supportStream]
    · rw [heq]
      simpa only [hvprod,high,supportFinished_stream,next,out] using he
  obtain ⟨k,hk,out,hi,hsrc,he⟩ := rawScan_eval 162 (supportStep produce) Squarefree.encodeMask
    next budget inv body ss seed
    (machine regs (emptyCore e) (supportStream base (Product.bytes seed) (rawFrames (ss.map Squarefree.encodeMask))))
    ⟨_,rfl⟩ (by simp [machine,supportStream,streamBits])
  obtain ⟨source,htapes⟩ := hi
  have hsource : source = [] := by
    have hh := (congrFun htapes 162).symm.trans hsrc
    simpa [machine,supportStream] using hh
  have hout : out = machine out.regs (emptyCore e)
      (supportStream base (Product.bytes (supportsRun p t M cache table u J meaning base hs one ss seed)) []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · simpa only [machine,hsource,next,supportsRun_foldl] using htapes
  refine ⟨k,hk,out.regs,?_⟩
  rw [hout] at he
  simpa only [supportScan] using he

end SubexponentialSAT.SqrtLog.MomentsAssembly


namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem supportsRun_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (a b : Fin 768 → List Bool) (h177 : a 177 = b 177) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (seed : List (Product.Entry n (baseWidth p t) d)) :
    supportsRun p t M cache table u J meaning a hs one ss seed =
      supportsRun p t M cache table u J meaning b hs one ss seed := by
  induction ss generalizing seed with
  | nil => rfl
  | cons s ss ih =>
      simp only [supportsRun,supportProduct_congr p t M cache table u J meaning a b h177,ih]

def bucketFinished (high : Fin 768 → List Bool) (tail result : List Bool) :=
  Function.update (Function.update high 163 tail) 166 result

def bucketStepValue (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one seed : List (Product.Entry n (baseWidth p t) d)) (b : BucketInput) :=
  supportsRun p t M cache table u J meaning (Function.update high 177 b.context) b.heads one ss seed

def bucketStepBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one seed : List (Product.Entry n (baseWidth p t) d)) (b : BucketInput) (tail : List Bool) :=
  bucketHeaderBudget high b +
    supportsWork p t M cache table u J meaning cost (bucketHigh high b tail) b.heads one ss seed +
    (2*b.context.length+3+(2*(rawFrames (b.heads.map HeadInput.bits)).length+3))

/-- One actual bucket tuple: decode it, run the full support computation, and
clear only its metadata and head master after all contributions are added. -/
theorem bucketStep_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (b : BucketInput) (tail : List Bool) (high : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hsrc : high 163 = Encoding.frame b.bits ++ tail)
    (hsupports : high 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : high 167 = Product.bytes one) (hseed : high 166 = Product.bytes seed)
    (hclean : SupportClean high) (h162 : high 162 = []) (h170 : high 170 = []) (h177 : high 177 = [])
    (hv : SupportFrames (n:=n) validFrame (bucketHigh high b tail) b.heads) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ bucketStepBudget p t M cache table u J meaning cost high ss one seed b tail, ∃ rr,
      Eval (bucketStep produce) k (machine regs (emptyCore e) high)
        (machine rr (emptyCore e)
          (bucketFinished high tail (Product.bytes (bucketStepValue p t M cache table u J meaning high ss one seed b)))) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let base := bucketHigh high b tail
  obtain ⟨r1,h1⟩ := startBucket_eval regs (emptyCore e) high b tail hsrc
    (hclean 164 (Or.inl (by decide))) (hclean 176 (Or.inl (by decide))) h177 h170 h162
    (hclean 179 (Or.inl (by decide)))
  have hc : SupportClean base := by
    intro i hi
    have h163 : i ≠ 163 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    have h162' : i ≠ 162 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    have h170' : i ≠ 170 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    have h177' : i ≠ 177 := by intro h; subst i; norm_num [Fin.ext_iff] at hi
    by_cases h176 : i = 176
    · subst i; simp [base,bucketHigh,bucketHigh3]
    · simpa [base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,h163,h162',h170',h177',h176]
        using hclean i hi
  obtain ⟨ns,hs,r2,h2⟩ := supportScan_eval produce p t M cache hz table degree width hd hw u J
    meaning cost validFrame contract one seed ss b.heads base r1
    (by simp [base,bucketHigh,bucketHigh3])
    (by simpa [base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1] using hone) hc hv
  have hb : supportStream base (Product.bytes seed) (rawFrames (ss.map Squarefree.encodeMask)) = base := by
    funext i
    by_cases hi : i = 166
    · subst i; simp [supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,hseed]
    by_cases hj : i = 162
    · subst i; simp [supportStream,base,bucketHigh,hsupports]
    simp [supportStream,hi,hj]
  rw [hb] at h2
  let result := bucketStepValue p t M cache table u J meaning high ss one seed b
  have hvresult : supportsRun p t M cache table u J meaning base b.heads one ss seed = result := by
    apply supportsRun_congr p t M cache table u J meaning base (Function.update high 177 b.context)
    simp [base,bucketHigh,bucketHigh3,bucketHigh2]
  rw [hvresult] at h2
  let afterSupports := supportStream base (Product.bytes result) []
  obtain ⟨r3,h3⟩ := finishBucket_eval r2 (emptyCore e) afterSupports
  have hout : Function.update (Function.update afterSupports 177 []) 170 [] =
      bucketFinished high tail (Product.bytes result) := by
    funext i
    by_cases ha : i = 166
    · subst i; simp [afterSupports,supportStream,bucketFinished]
    by_cases hb : i = 170
    · subst i; simp [bucketFinished,h170]
    by_cases hc : i = 177
    · subst i; simp [bucketFinished,h177]
    by_cases hd : i = 162
    · subst i; simp [afterSupports,supportStream,bucketFinished,h162]
    by_cases he : i = 176
    · subst i
      simp [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketFinished,
        hclean 176 (Or.inl (by decide))]
    by_cases hf : i = 163
    · subst i; simp [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,bucketFinished]
    simp [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,bucketFinished,ha,hb,hc,hd,he,hf]
  have h3' : Eval finishBucket (2*b.context.length+3+(2*(rawFrames (b.heads.map HeadInput.bits)).length+3))
      (machine r2 (emptyCore e) afterSupports)
      (machine r3 (emptyCore e) (bucketFinished high tail (Product.bytes result))) := by
    rw [hout] at h3
    simpa [afterSupports,supportStream,base,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1] using h3
  refine ⟨bucketHeaderBudget high b+(ns+
    (2*b.context.length+3+(2*(rawFrames (b.heads.map HeadInput.bits)).length+3))),?_,r3,?_⟩
  · dsimp [bucketStepBudget]
    dsimp [base] at hs
    omega
  · simpa only [bucketStep,afterSupports,result] using h1.seq (h2.seq h3')

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def bucketStream (base : Fin 768 → List Bool) (seed source : List Bool) :=
  Function.update (Function.update base 163 source) 166 seed

theorem bucketFinished_stream (base : Fin 768 → List Bool) (seed source tail result : List Bool) :
    bucketFinished (bucketStream base seed source) tail result = bucketStream base result tail := by
  funext i
  by_cases h1 : i=166
  · subst i; simp [bucketFinished,bucketStream]
  by_cases h2 : i=163
  · subst i; simp [bucketFinished,bucketStream]
  simp [bucketFinished,bucketStream,h1,h2]

theorem supportsWork_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (a b : Fin 768 → List Bool) (h170 : a 170 = b 170) (h177 : a 177 = b 177)
    (hs : List HeadInput) (one : List (Product.Entry n (baseWidth p t) d))
    (ss : List (Finset (Fin n))) (seed : List (Product.Entry n (baseWidth p t) d)) :
    supportsWork p t M cache table u J meaning cost a hs one ss seed =
      supportsWork p t M cache table u J meaning cost b hs one ss seed := by
  unfold supportsWork
  have hcost : (fun seed s => supportStepBudget p t M cache table u J meaning cost a hs [] one seed s) =
      (fun seed s => supportStepBudget p t M cache table u J meaning cost b hs [] one seed s) := by
    funext seed s
    exact supportStepBudget_congr p t M cache table u J meaning cost a b h170 h177 hs [] [] one seed s
  have hstep : (fun seed s => supportValue p t M cache s
      (supportProduct p t M cache table u J meaning a hs one s) seed) =
      (fun seed s => supportValue p t M cache s
        (supportProduct p t M cache table u J meaning b hs one s) seed) := by
    funext seed s
    rw [supportProduct_congr p t M cache table u J meaning a b h177]
  rw [hcost,hstep]

theorem bucketStepValue_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (a b : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one seed : List (Product.Entry n (baseWidth p t) d)) (bucket : BucketInput) :
    bucketStepValue p t M cache table u J meaning a ss one seed bucket =
      bucketStepValue p t M cache table u J meaning b ss one seed bucket := by
  exact supportsRun_congr p t M cache table u J meaning _ _ (by simp) _ _ _ _

theorem bucketStepBudget_congr (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (a b : Fin 768 → List Bool) (h169 : a 169 = b 169) (ss : List (Finset (Fin n)))
    (one seed : List (Product.Entry n (baseWidth p t) d)) (bucket : BucketInput) (ta tb : List Bool) :
    bucketStepBudget p t M cache table u J meaning cost a ss one seed bucket ta =
      bucketStepBudget p t M cache table u J meaning cost b ss one seed bucket tb := by
  have hw := supportsWork_congr p t M cache table u J meaning cost
    (bucketHigh a bucket ta) (bucketHigh b bucket tb)
    (by simp [bucketHigh,bucketHigh3]) (by simp [bucketHigh,bucketHigh3,bucketHigh2])
    bucket.heads one ss seed
  simp only [bucketStepBudget,bucketHeaderBudget,h169,hw]

theorem bucketsRun_foldl (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (base : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d)) (bs : List BucketInput)
    (seed : List (Product.Entry n (baseWidth p t) d)) :
    bs.foldl (fun a b => bucketStepValue p t M cache table u J meaning base ss one a b) seed =
      bucketsRun p t M cache table u J meaning base ss one bs seed := by
  induction bs generalizing seed with
  | nil => rfl
  | cons b bs ih => simpa only [List.foldl,bucketsRun,bucketStepValue] using ih (bucketStepValue p t M cache table u J meaning base ss one seed b)

def bucketsWork (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (base : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d)) (bs : List BucketInput)
    (seed : List (Product.Entry n (baseWidth p t) d)) :=
  scanWork (fun a (b : {b // b ∈ bs}) => bucketStepBudget p t M cache table u J meaning cost base ss one a b.val [])
    (fun a (b : {b // b ∈ bs}) => bucketStepValue p t M cache table u J meaning base ss one a b.val)
    seed bs.attach+1

def BucketFrames {n : ℕ} (valid : (Fin 768 → List Bool) → Prop)
    (base : Fin 768 → List Bool) (bs : List BucketInput) : Prop :=
  ∀ b ∈ bs, ∀ seed source tail,
    SupportFrames (n:=n) valid (bucketHigh (bucketStream base seed source) b tail) b.heads

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- Complete physical bucket/support/head/assignment nesting. The sole
callback is the paid per-assignment producer; all moment arithmetic and
metadata movement are the concrete commands proved above. -/
theorem command_eval (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (n:=n) validFrame base bs) :
    let e := Product.environment p t M cache table degree width u J
    ∃ k ≤ bucketsWork p t M cache table u J meaning cost base ss one bs seed, ∃ rr,
      Eval (command produce) k
        (machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs)))
        (machine rr (emptyCore e)
          (bucketStream base (Product.bytes (bucketsRun p t M cache table u J meaning base ss one bs seed)) [])) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let encode := fun b : {b // b ∈ bs} => b.val.bits
  let next := fun (a : List (Product.Entry n (baseWidth p t) d)) (b : {b // b ∈ bs}) =>
    bucketStepValue p t M cache table u J meaning base ss one a b.val
  let budget := fun (a : List (Product.Entry n (baseWidth p t) d)) (b : {b // b ∈ bs}) =>
    bucketStepBudget p t M cache table u J meaning cost base ss one a b.val []
  let inv := fun (a : List (Product.Entry n (baseWidth p t) d)) (tapes : Fin 768 → List Bool) =>
    ∃ source, tapes = (machine (fun _ => false) (emptyCore e)
      (bucketStream base (Product.bytes a) source)).stacks
  have hbits : streamBits encode bs.attach = bucketsInput bs := by
    unfold streamBits bucketsInput
    congr 1
    calc
      bs.attach.map encode = (bs.attach.map Subtype.val).map BucketInput.bits := by
        simp only [List.map_map,encode,Function.comp_def]
      _ = bs.map BucketInput.bits := by rw [List.attach_map_subtype_val]
  have body : BodyContract 163 (bucketStep produce) encode next budget inv := by
    intro a b tail state hi hsrc
    obtain ⟨source,htapes⟩ := hi
    have hsource : source = Encoding.frame b.val.bits ++ tail := by
      have he := (congrFun htapes 163).symm.trans hsrc
      simpa [machine,bucketStream,encode] using he
    subst source
    let high := bucketStream base (Product.bytes a) (Encoding.frame b.val.bits ++ tail)
    have heq : state = machine state.regs (emptyCore e) high := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · exact htapes
    have hc : SupportClean high := by
      intro i hi
      have hn163 : i ≠ 163 := by intro he; subst i; norm_num [Fin.ext_iff] at hi
      have hn166 : i ≠ 166 := by intro he; subst i; norm_num [Fin.ext_iff] at hi
      simpa [high,bucketStream,hn163,hn166] using hclean i hi
    obtain ⟨k,hk,rr,he⟩ := bucketStep_eval produce p t M cache hz table degree width hd hw u J
      meaning cost validFrame contract one a ss b.val tail high state.regs
      (by simp [high,bucketStream]) (by simpa [high,bucketStream] using hsupports)
      (by simpa [high,bucketStream] using hone) (by simp [high,bucketStream]) hc
      (by simp [high,bucketStream,h162]) (by simp [high,bucketStream,h170])
      (by simp [high,bucketStream,h177]) (hv b.val b.property (Product.bytes a) _ tail)
    have hvalue : bucketStepValue p t M cache table u J meaning high ss one a b.val = next a b :=
      bucketStepValue_congr p t M cache table u J meaning high base ss one a b.val
    have hbound : k ≤ budget a b := by
      simpa only [budget,bucketStepBudget_congr p t M cache table u J meaning cost high base
        (by simp [high,bucketStream]) ss one a b.val tail []] using hk
    let out := machine rr (emptyCore e) (bucketStream base (Product.bytes (next a b)) tail)
    refine ⟨k,hbound,out,⟨tail,rfl⟩,?_,?_⟩
    · simp [out,machine,bucketStream]
    · rw [heq]
      simpa only [hvalue,high,bucketFinished_stream,out] using he
  obtain ⟨k,hk,out,hi,hsrc,he⟩ := rawScan_eval 163 (bucketStep produce) encode
    next budget inv body bs.attach seed
    (machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs)))
    ⟨_,rfl⟩ (by simp [machine,bucketStream,hbits])
  have hfold : bs.attach.foldl next seed = bucketsRun p t M cache table u J meaning base ss one bs seed := by
    calc
      bs.attach.foldl next seed = (bs.attach.map Subtype.val).foldl
        (fun a b => bucketStepValue p t M cache table u J meaning base ss one a b) seed := by
          simp only [List.foldl_map,next]
      _ = bs.foldl (fun a b => bucketStepValue p t M cache table u J meaning base ss one a b) seed := by
        rw [List.attach_map_subtype_val]
      _ = _ := bucketsRun_foldl p t M cache table u J meaning base ss one bs seed
  obtain ⟨source,htapes⟩ := hi
  have hsource : source = [] := by
    have hh := (congrFun htapes 163).symm.trans hsrc
    simpa [machine,bucketStream] using hh
  have hout : out = machine out.regs (emptyCore e)
      (bucketStream base (Product.bytes (bucketsRun p t M cache table u J meaning base ss one bs seed)) []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · simpa only [machine,hsource,hfold] using htapes
  refine ⟨k,hk,out.regs,?_⟩
  rw [hout] at he
  simpa only [command] using he

/-- A finite compiled machine with the exact recursive runtime bound. The
producer is a fixed finite command, not a semantic oracle. -/
theorem program_run (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (n:=n) validFrame base bs) :
    let e := Product.environment p t M cache table degree width u J
    ∃ rr, RunsIn (program produce) (bucketsWork p t M cache table u J meaning cost base ss one bs seed+1)
      ((machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs))).withPC
        (some (program produce).entry))
      ((machine rr (emptyCore e)
        (bucketStream base (Product.bytes (bucketsRun p t M cache table u J meaning base ss one bs seed)) [])).withPC none) := by
  dsimp only
  obtain ⟨k,hk,rr,he⟩ := command_eval produce p t M cache hz table degree width hd hw u J meaning cost
    validFrame contract one seed ss bs base regs hsupports hone hclean h162 h170 h177 hv
  exact ⟨rr,k+1,Nat.add_le_add_right hk 1,compiled_halt_trace he 163 166⟩

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
