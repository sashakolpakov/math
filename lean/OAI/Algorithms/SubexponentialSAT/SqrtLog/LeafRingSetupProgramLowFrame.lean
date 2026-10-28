import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

namespace OAI.Algorithms


/-! The ring producer can clear low arithmetic workspace, but never inserts
data there.  Thus initially blank low node-work tapes stay blank.  This is a
property of the existing program, not an additional cleanup operation. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame
open BitProgram StructuredCalls

structure EmptyPreserved {r s : ℕ} (c : Cmd r s) (i : Fin s) : Prop where
  run : ∀ {n : ℕ} {a b : State r s}, Eval c n a b → a.stacks i=[] → b.stacks i=[]

theorem seq {r s : ℕ} {c d : Cmd r s} {i : Fin s}
    (hc : EmptyPreserved c i) (hd : EmptyPreserved d i) :
    EmptyPreserved (.seq c d) i := by
  constructor
  intro n a b h hz
  cases h with
  | seq h1 h2 => exact hd.run h2 (hc.run h1 hz)

theorem skip {r s : ℕ} (i : Fin s) : EmptyPreserved (.base (.skip : StructuredProgram.Cmd r s)) i := by
  constructor
  intro n a b h hz
  cases h with
  | base h => cases h; exact hz

theorem trace_empty {r s l : ℕ} (p : Program r s l) (i : Fin s)
    (hp : ∀ q c, c.stacks i=[] → (execInstr (p.code q) c).stacks i=[])
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hz : a.stacks i=[]) :
    b.stacks i=[] := by
  induction h with
  | refl => exact hz
  | @cons k a z b hs ht ih =>
    apply ih
    cases hpc : a.pc with
    | none => simp [step,hpc] at hs
    | some q =>
      have he : execInstr (p.code q) a=z := by simpa [step,hpc] using hs
      exact he ▸ hp q a hz

theorem call {r s l : ℕ} (p : Program r s l) (i : Fin s)
    (hp : ∀ q c, c.stacks i=[] → (execInstr (p.code q) c).stacks i=[]) :
    EmptyPreserved (.call p) i := by
  constructor
  intro n a b h hz
  cases h with
  | call _ ht => exact trace_empty p i hp ht hz

theorem lifted {r s R S l : ℕ} (p : Program r s l)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (i : Fin S)
    (hi : ∀ j, i≠stk j) :
    EmptyPreserved (.call (ProgramLinking.liftProgram p reg stk)) i := by
  apply call
  intro q c hz
  change (execInstr (ProgramLinking.relocateInstr reg stk id none (p.code q)) c).stacks i=[]
  cases p.code q <;> simp [ProgramLinking.relocateInstr,execInstr,hi,hz]

theorem highLift {r s l : ℕ} (p : Program r s l)
    (reg : Fin r → Fin 32) (stk : Fin s → Fin 640) (i : Fin 640)
    (hi : i.val < 190) (hs : ∀ j,190 ≤ (stk j).val) :
    EmptyPreserved (.call (ProgramLinking.liftProgram p reg stk)) i := by
  apply lifted
  intro j he
  have hv := congrArg Fin.val he
  have := hs j
  omega

theorem clear (dst i : Fin 640) : EmptyPreserved (LeafRingSetupProgram.clear dst) i := by
  apply call
  intro q c hz
  by_cases he : i=dst
  · subst i
    fin_cases q <;> simp [execInstr,hz]
  · fin_cases q <;> simp [execInstr,hz,he]

theorem copy (src dst i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (hd : 190 ≤ dst.val) :
    EmptyPreserved (LeafRingSetupProgram.copy src dst) i := by
  have hsrc : i≠src := by intro h; subst i; omega
  have hdst : i≠dst := by intro h; subst i; omega
  have htmp : i≠639 := by intro h; subst i; change (639:ℕ) < 190 at hi; omega
  apply call
  intro q c hz
  fin_cases q <;> simp [execInstr,hz,hsrc,hdst,htmp]

theorem overwrite (src dst i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (hd : 190 ≤ dst.val) :
    EmptyPreserved (LeafRingSetupProgram.overwrite src dst) i :=
  seq (clear dst i) (copy src dst i hi hs hd)

theorem clearPorts (ps : List (Fin 640)) (i : Fin 640) :
    EmptyPreserved (LeafRingSetupProgram.clearPorts ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih => exact seq (clear p i) ih

theorem reset {r s : ℕ} (ps : List (Fin r)) (i : Fin s) :
    EmptyPreserved (RegisterResetProgram.clear ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih =>
    unfold RegisterResetProgram.clear
    apply seq _ ih
    constructor
    intro n a b h hz
    cases h with
    | base h => cases h; exact hz

theorem resetAll (i : Fin 640) : EmptyPreserved (RegisterResetProgram.all : Cmd 32 640) i :=
  reset _ i

theorem unary (src dst i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (hd : 190 ≤ dst.val) :
    EmptyPreserved (LeafRingSetupProgram.unary src dst) i := by
  apply highLift _ _ _ i hi
  intro j
  unfold unaryPorts
  split_ifs <;> (try dsimp only) <;> omega

theorem unaryPlan (ps : List (Fin 640 × Fin 640)) (i : Fin 640) (hi : i.val < 190)
    (hp : ∀ p∈ps,190 ≤ p.1.val ∧ 190 ≤ p.2.val) :
    EmptyPreserved (LeafRingSetupProgram.unaryPlan ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih =>
    exact seq (unary p.1 p.2 i hi (hp p (by simp)).1 (hp p (by simp)).2)
      (ih (fun q hq => hp q (by simp [hq])))

theorem copyPlan (ps : List (Fin 640 × Fin 640)) (i : Fin 640) (hi : i.val < 190)
    (hp : ∀ p∈ps,190 ≤ p.1.val ∧ 190 ≤ p.2.val) :
    EmptyPreserved (LeafRingSetupProgram.copyPlan ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih =>
    exact seq (overwrite p.1 p.2 i hi (hp p (by simp)).1 (hp p (by simp)).2)
      (ih (fun q hq => hp q (by simp [hq])))

theorem number (i : Fin 640) (hi : i.val < 190) : EmptyPreserved numberPhase i := by
  unfold numberPhase
  have hs : EmptyPreserved serializationCall i := by
    apply highLift _ _ _ i hi
    intro j
    change 190 ≤ 340+j.val
    omega
  have hu : EmptyPreserved (LeafRingSetupProgram.unaryPlan numericPlan) i :=
    unaryPlan numericPlan i hi (by
      intro p hp
      simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide)
  exact seq (clearPorts _ i) (seq hs (seq hu (seq
    (overwrite 373 511 i hi (by decide) (by decide)) (resetAll i))))

theorem core (i : Fin 640) (hi : i.val < 190) : EmptyPreserved coreCommand i := by
  unfold coreCommand searchAndPad
  have hs : ∀ j,190 ≤ (scalar j).val := by intro j; unfold scalar; split_ifs <;> (try dsimp only) <;> omega
  have hh : ∀ j,190 ≤ (search j).val := by intro j; unfold search; split_ifs <;> (try dsimp only) <;> omega
  have ht : ∀ j,190 ≤ (table j).val := by intro j; unfold table; split_ifs <;> (try dsimp only) <;> omega
  have sc : EmptyPreserved scalarCall i := highLift _ _ _ i hi hs
  have se : EmptyPreserved searchCall i := highLift _ _ _ i hi hh
  have pa : EmptyPreserved paddingCall i := highLift _ _ _ i hi hh
  have ta : EmptyPreserved tableCall i := highLift _ _ _ i hi ht
  exact seq sc (seq (overwrite 507 253 i hi (by decide) (by decide)) (seq (resetAll i)
    (seq (seq se (seq (overwrite 202 432 i hi (by decide) (by decide)) pa))
      (seq (overwrite 498 538 i hi (by decide) (by decide)) ta))))

theorem buildConstant (src out i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (ho : 190 ≤ out.val) :
    EmptyPreserved (LeafRingSetupProgram.buildConstant src out) i := by
  apply seq (overwrite src 538 i hi hs (by decide))
  apply highLift _ _ _ i hi
  intro j
  unfold constant
  split_ifs <;> (try dsimp only) <;> omega

theorem constants (i : Fin 640) (hi : i.val < 190) : EmptyPreserved constantsPhase i :=
  seq (clearPorts _ i) (seq
    (seq (buildConstant 498 207 i hi (by decide) (by decide))
      (seq (buildConstant 508 211 i hi (by decide) (by decide))
        (buildConstant 203 280 i hi (by decide) (by decide))))
    (copyPlan constantAliases i hi (by
      intro p hp
      simp only [constantAliases,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> decide)))

theorem nodes (i : Fin 640) (hi : i.val < 190) : EmptyPreserved nodesPhase i := by
  have hn : EmptyPreserved nodesCall i := by
    apply highLift _ _ _ i hi
    intro j
    unfold LeafRingSetupProgram.nodes
    split_ifs <;> (try dsimp only) <;> omega
  have hf : EmptyPreserved nodeFramesCall i := by
    apply highLift _ _ _ i hi
    intro j
    fin_cases j <;> decide
  exact seq (clearPorts _ i) (seq (copyPlan nodeInputs i hi (by
      intro p hp
      simp only [nodeInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> decide))
    (seq hn (seq (overwrite 256 628 i hi (by decide) (by decide))
      (seq hf (overwrite 628 256 i hi (by decide) (by decide))))))

theorem idempotents (i : Fin 640) (hi : i.val < 190) : EmptyPreserved idempotentPhase i := by
  unfold idempotentPhase
  have h : EmptyPreserved idempotentCall i := by
    apply highLift _ _ _ i hi
    intro j
    change 190 ≤ 480+j.val
    omega
  exact seq (clearPorts _ i) (seq (overwrite 373 511 i hi (by decide) (by decide))
    (seq (resetAll i) (seq h (overwrite 512 281 i hi (by decide) (by decide)))))

theorem producerCommand_preservesEmpty (i : Fin 640) (hi : i.val < 190) :
    EmptyPreserved producerCommand i :=
  seq (number i hi) (seq (core i hi) (seq (constants i hi) (seq (nodes i hi)
    (seq (idempotents i hi) (seq (clearPorts _ i) (resetAll i))))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
