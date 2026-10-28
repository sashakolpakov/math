import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticNegMachine
import OAI.Algorithms.SubexponentialSAT.FourWordPrograms
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Four-word negation with measured copying, splitting, packing, and cleanup.
The input quartet and the prepared minus-one word are both preserved. -/

namespace SubexponentialSAT.SubexpQuarticFlatNeg

open BitProgram StackRoutines StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpQuarticMachine FourWordPrograms

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

def wordLists {B : ℕ} (a : Quad (Word B)) : Words := fun i => (a.toFn i).val
def flat {B : ℕ} (a : Quad (Word B)) : List Bool := flatWords (wordLists a)

@[simp] theorem wordLists_length {B : ℕ} (a : Quad (Word B)) (i : Fin 4) :
    (wordLists a i).length = B := (a.toFn i).property

@[simp] theorem flat_length {B : ℕ} (a : Quad (Word B)) : (flat a).length = 4 * B := by
  simp [flat, flatWords]
  omega

def initialBank {B : ℕ} (a : Quad (Word B)) (one : Word B) : Fin 9 → Word B :=
  ![a.c0,a.c1,a.c2,a.c3,one,a.c0,a.c0,a.c0,a.c0]

def partialBank {B : ℕ} (a : Quad (Word B)) (one : Word B) : Fin 9 → List Bool :=
  ![a.c0.val,a.c1.val,a.c2.val,a.c3.val,one.val,[],[],[],[]]

def emptyBank (one : List Bool) : Fin 9 → List Bool := ![[],[],[],[],one,[],[],[],[]]

/-- Constant 4, modulus 14, original input 18, output 19, and width 20. -/
def bankStore (bank : Fin 9 → List Bool) (modulus beta width result : List Bool)
    (i : Fin 24) : List Bool :=
  if h : i.val < 9 then bank ⟨i.val,h⟩
  else if i = 14 then modulus
  else if i = 18 then beta
  else if i = 19 then result
  else if i = 20 then width
  else []

def initialStore {B : ℕ} (a : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) : Stacks (Fin 24) :=
  bankStore (emptyBank one.val) modulus (flat a) width []

def finalStore {B : ℕ} (a result : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) : Stacks (Fin 24) :=
  bankStore (emptyBank one.val) modulus (flat a) width (flat result)

def splitPorts : Fin 8 ↪ Fin 24 := ⟨![22,20,21,17,0,1,2,3], by decide⟩
def packPorts : Fin 8 ↪ Fin 24 := ⟨![19,20,21,17,5,6,7,8], by decide⟩
def bankPorts : Fin 18 ↪ Fin 24 := ⟨Fin.castAdd 6, Fin.castAdd_injective 18 6⟩
def tempSlots : List (Fin 24) := [5,6,7,8]
def clearSlots : List (Fin 24) := [0,1,2,3,5,6,7,8]

abbrev prepareCmd : Cmd 8 24 :=
  .seq (.call (copyProgram 18 22 17 0 1))
    (.seq (splitCmd splitPorts 0 1) (BankRoutines.fillCmd 0 17 0 1 tempSlots))

theorem prepare_eval {B : ℕ} (a : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) (hw : width.length = B) (regs : Fin 8 → Bool) :
    Eval prepareCmd (112 * B + 72) ⟨regs, initialStore a one modulus width⟩
      ⟨readRegs regs 0 1 none,
        bankStore (fun i => (initialBank a one i).val) modulus (flat a) width []⟩ := by
  let d : State 8 24 := ⟨regs, initialStore a one modulus width⟩
  let d₁ := afterCopy d 18 22 0 1
  have hc := copy_eval d 18 22 17 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d, initialStore, bankStore])
  have hs := split_eval splitPorts 0 1 (by decide) (wordLists a) [] width d₁.regs d₁.stacks
    (by simp [d₁,d,afterCopy,copyStacks,initialStore,bankStore,splitPorts,flat])
    (by simp [d₁,d,afterCopy,copyStacks,initialStore,bankStore,splitPorts])
    (by intro i; simp [hw])
    (by simp [d₁,d,afterCopy,copyStacks,initialStore,bankStore,splitPorts])
    (by simp [d₁,d,afterCopy,copyStacks,initialStore,bankStore,splitPorts])
  have hsplit :
      (⟨readRegs d₁.regs 0 1 none, splitStacks splitPorts (wordLists a) [] d₁.stacks⟩ :
        State 8 24) =
      ⟨readRegs regs 0 1 none, bankStore (partialBank a one) modulus (flat a) width []⟩ := by
    apply state_ext
    · simp [d₁,d,afterCopy,readRegs_reset]
    · funext i
      fin_cases i <;> simp [d₁,d,afterCopy,copyStacks,initialStore,bankStore,emptyBank,
        splitStacks,splitPorts,partialBank,wordLists,Quad.toFn]
  rw [hsplit] at hs
  have hf := BankRoutines.fill_eval (0 : Fin 24) 17 (0 : Fin 8) 1 tempSlots
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (readRegs regs 0 1 none) (bankStore (partialBank a one) modulus (flat a) width [])
    (by
      intro i hi
      simp only [tempSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;>
      simp [bankStore,partialBank]) (by simp [bankStore])
  have hfill : BankRoutines.fillStacks 0 tempSlots
      (bankStore (partialBank a one) modulus (flat a) width []) =
      bankStore (fun i => (initialBank a one i).val) modulus (flat a) width [] := by
    funext i
    fin_cases i <;> simp [BankRoutines.fillStacks,tempSlots,bankStore,partialBank,initialBank]
  have total := hc.seq (hs.seq hf)
  simp only [readRegs_reset,hfill] at total
  dsimp [prepareCmd]
  convert total using 1
  all_goals
    simp [d,initialStore,bankStore,partialBank,tempSlots,hw,flat_length,a.c0.property]
    omega

abbrev finishCmd : Cmd 8 24 :=
  .seq (packCmd packPorts 0 1) (BankRoutines.clearCmd 17 0 1 clearSlots)

theorem output_words {B : ℕ} (bank : Fin 9 → Word B) (modulus beta width : List Bool) :
    bankWords packPorts (bankStore (fun i => (bank i).val) modulus beta width []) =
      wordLists (SubexpQuarticNegMachine.output bank) := by
  funext i
  fin_cases i <;> simp [bankWords,wordPort,packPorts,bankStore,wordLists,
    SubexpQuarticNegMachine.output,Quad.toFn]

theorem finish_eval {B : ℕ} (bank : Fin 9 → Word B) (modulus beta width : List Bool)
    (regs : Fin 8 → Bool) :
    Eval finishCmd (44 * B + 47)
      ⟨regs, bankStore (fun i => (bank i).val) modulus beta width []⟩
      ⟨readRegs regs 0 1 none, bankStore (emptyBank (bank 4).val) modulus beta width
        (flat (SubexpQuarticNegMachine.output bank))⟩ := by
  let stk := bankStore (fun i => (bank i).val) modulus beta width []
  have hp := pack_eval packPorts 0 1 (by decide) regs stk (by simp [stk,packPorts,bankStore])
  have hpack : packStacks packPorts stk =
      bankStore (fun i => (bank i).val) modulus beta width
        (flat (SubexpQuarticNegMachine.output bank)) := by
    funext i
    by_cases hi : i = 19
    · subst i
      change flatWords (bankWords packPorts stk) ++ stk 19 = _
      rw [output_words]
      simp [stk,bankStore,flat]
    · simp [packStacks,packPorts,stk,bankStore,hi]
  have hlen : (flatWords (bankWords packPorts stk)).length = 4 * B := by
    rw [output_words]
    exact flat_length _
  have hc := BankRoutines.clear_eval_uniform (17 : Fin 24) (0 : Fin 8) 1 clearSlots
    (by decide) (readRegs regs 0 1 none)
    (bankStore (fun i => (bank i).val) modulus beta width
      (flat (SubexpQuarticNegMachine.output bank))) B
    (by
      intro i hi
      simp only [clearSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simpa [bankStore] using (bank _).property)
    (by simp [bankStore])
  have hclear : BankRoutines.clearBankStacks clearSlots
      (bankStore (fun i => (bank i).val) modulus beta width
        (flat (SubexpQuarticNegMachine.output bank))) =
      bankStore (emptyBank (bank 4).val) modulus beta width
        (flat (SubexpQuarticNegMachine.output bank)) := by
    funext i
    fin_cases i <;> simp [BankRoutines.clearBankStacks,clearSlots,bankStore,emptyBank]
  rw [hpack] at hp
  have total := hp.seq hc
  simp only [readRegs_reset,hclear,hlen] at total
  dsimp [finishCmd]
  convert total using 1
  all_goals
    simp [clearSlots]
    omega

theorem bankStore_native (bank : Fin 9 → List Bool) (modulus beta width result : List Bool)
    (i : Fin 18) :
    bankStore bank modulus beta width result (bankPorts i) =
      SubexpQuarticMachine.store bank (scalarWork [] [] modulus) [] i := by
  refine Fin.addCases (m := 9) (n := 9) (fun j => ?_) (fun j => ?_) i
  · change bankStore bank modulus beta width result (Fin.castAdd 15 j) =
      SubexpQuarticMachine.store bank (scalarWork [] [] modulus) [] (bankPort j)
    simp [bankStore]
  · fin_cases j <;>
      simp [bankStore,bankPorts,SubexpQuarticMachine.store,scalarWork,Fin.addCases] <;> rfl

theorem embed_bank {B : ℕ} (regs frameRegs : Fin 8 → Bool)
    (bank : Fin 9 → Word B) (frameBank : Fin 9 → List Bool)
    (modulus beta width result : List Bool) :
    embedState id bankPorts ⟨frameRegs,bankStore frameBank modulus beta width result⟩
      (restingState regs bank modulus) =
      ⟨regs,bankStore (fun i => (bank i).val) modulus beta width result⟩ := by
  apply embedState_eq id bankPorts Function.injective_id bankPorts.injective
  · intro i; rfl
  · intro i
    simpa only [restingState] using
      bankStore_native (fun j => (bank j).val) modulus beta width result i
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i hi
    have hn : ¬ i.val < 18 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,rfl⟩
    have hb : ¬ i.val < 9 := by omega
    simp [bankStore,hb]

abbrev bankCall : Cmd 8 24 :=
  .call (ProgramLinking.liftProgram SubexpQuarticNegMachine.program id bankPorts)

theorem bankCall_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (bank : Fin 9 → Word (baseWidth p μ)) (regs : Fin 8 → Bool) (beta width : List Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 24401 * (baseWidth p μ + 1)^2 ∧
      Eval bankCall n ⟨regs,bankStore (fun i => (bank i).val) M.bits beta width []⟩
        ⟨rf,bankStore
          (fun i => (scriptEval p μ M SubexpQuarticNegMachine.negCode bank i).val)
          M.bits beta width []⟩ := by
  obtain ⟨rf,n,hn,ht⟩ := SubexpQuarticNegMachine.program_run p μ M regs bank
  have h := eval_call_lifted SubexpQuarticNegMachine.program id bankPorts
    (⟨regs,bankStore (fun i => (bank i).val) M.bits beta width []⟩ : State 8 24)
    Function.injective_id bankPorts.injective
    (a := restingState regs bank M.bits)
    (b := restingState rf (scriptEval p μ M SubexpQuarticNegMachine.negCode bank) M.bits)
    (n := n) ht
  exact ⟨n,rf,hn,by simpa only [bankCall,embed_bank] using h⟩

abbrev command : Cmd 8 24 := .seq prepareCmd (.seq bankCall finishCmd)
abbrev program : Program 8 24 (size command + 1) := compiled command 18 19

theorem command_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (one : Word (baseWidth p μ))
    (width : List Bool) (hw : width.length = baseWidth p μ) (regs : Fin 8 → Bool) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n + 1 ≤ 25000 * (baseWidth p μ + 1)^2 ∧
      Eval command n ⟨regs,initialStore a one M.bits width⟩
        ⟨rf,finalStore a (SubexpQuarticNegMachine.negateWords p μ M one a) one M.bits width⟩ := by
  have hp := prepare_eval a one M.bits width hw regs
  obtain ⟨n,rf,hn,hb⟩ := bankCall_eval p μ M (initialBank a one)
    (readRegs regs 0 1 none) (flat a) width
  have hf := finish_eval (scriptEval p μ M SubexpQuarticNegMachine.negCode (initialBank a one))
    M.bits (flat a) width rf
  have hout : SubexpQuarticNegMachine.output
      (scriptEval p μ M SubexpQuarticNegMachine.negCode (initialBank a one)) =
      SubexpQuarticNegMachine.negateWords p μ M one a := by
    rw [SubexpQuarticNegMachine.negCode_correct]
    cases a
    rfl
  have hone : scriptEval p μ M SubexpQuarticNegMachine.negCode (initialBank a one) 4 = one := by
    rw [SubexpQuarticNegMachine.negCode_frame _ _ _ _ _ (by decide)]
    rfl
  rw [hout,hone] at hf
  refine ⟨n + 156 * baseWidth p μ + 119, readRegs rf 0 1 none, ?_, ?_⟩
  · have hs := Nat.le_mul_self (baseWidth p μ + 1)
    rw [← pow_two] at hs
    omega
  · have ht := hp.seq (hb.seq hf)
    change Eval command _ _ _ at ht
    convert ht using 1
    · omega
    · rfl

theorem program_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (one : Word (baseWidth p μ))
    (width : List Bool) (hw : width.length = baseWidth p μ) (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn program (25000 * (baseWidth p μ + 1)^2)
      ⟨some program.entry,regs,initialStore a one M.bits width⟩
      ⟨none,rf,finalStore a (SubexpQuarticNegMachine.negateWords p μ M one a) one M.bits width⟩ := by
  obtain ⟨n,rf,hn,ht⟩ := command_run p μ M a one width hw regs
  exact ⟨rf,n+1,hn,compiled_halt_trace ht 18 19⟩

noncomputable def primitiveConstant : ℕ := primitiveOverhead program * 25000

theorem primitive_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (one : Word (baseWidth p μ))
    (width : List Bool) (hw : width.length = baseWidth p μ) (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveConstant * (baseWidth p μ + 1)^2)
      (primitiveCfg program ⟨some program.entry,regs,initialStore a one M.bits width⟩)
      (primitiveCfg program
        ⟨none,rf,finalStore a (SubexpQuarticNegMachine.negateWords p μ M one a) one M.bits width⟩) := by
  obtain ⟨rf,ht⟩ := program_run p μ M a one width hw regs
  refine ⟨rf, Computation.RunsIn.mono (BitProgram.primitive_execution program ht) ?_⟩
  unfold primitiveConstant
  rw [Nat.mul_assoc]

@[simp] theorem final_original {B : ℕ} (a result : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) : finalStore a result one modulus width 18 = flat a := by
  simp [finalStore,bankStore]

@[simp] theorem final_result {B : ℕ} (a result : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) : finalStore a result one modulus width 19 = flat result := by
  simp [finalStore,bankStore]

@[simp] theorem final_minusOne {B : ℕ} (a result : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) : finalStore a result one modulus width 4 = one.val := by
  simp [finalStore,bankStore,emptyBank]

theorem finalStore_update {B : ℕ} (a result : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) :
    finalStore a result one modulus width =
      Function.update (initialStore a one modulus width) 19 (flat result) := by
  funext i
  by_cases hi : i = 19
  · subst i
    simp [finalStore,initialStore,bankStore]
  · simp [finalStore,initialStore,bankStore,hi]

theorem final_scratch {B : ℕ} (a result : Quad (Word B)) (one : Word B)
    (modulus width : List Bool) (i : Fin 24)
    (h4 : i ≠ 4) (h14 : i ≠ 14) (h18 : i ≠ 18) (h19 : i ≠ 19) (h20 : i ≠ 20) :
    finalStore a result one modulus width i = [] := by
  fin_cases i <;> simp_all [finalStore,bankStore,emptyBank]

abbrev programAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 24 ↪ Fin s) :
    Program r s (size command + 1) :=
  ProgramLinking.liftProgram program registers ports

abbrev callAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 24 ↪ Fin s) : Cmd r s :=
  .call (programAt registers ports)

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [f.injective.extend_apply,h]
  · exact Function.extend_apply' _ _ _ hj

/-- Call the complete service inside an arbitrary larger machine. Only the
mapped output stack changes; unassigned Boolean registers are also framed. -/
theorem callAt_eval {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 24 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (one : Word (baseWidth p μ))
    (width : List Bool) (hw : width.length = baseWidth p μ) (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) = initialStore a one M.bits width i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool), n ≤ 25000 * (baseWidth p μ + 1)^2 ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          Function.update d.stacks (ports 19)
            (flat (SubexpQuarticNegMachine.negateWords p μ M one a))⟩ := by
  obtain ⟨rf,n,hn,ht⟩ := program_run p μ M a one width hw (fun i => d.regs (registers i))
  have hl := ProgramLinking.liftProgram_trace program registers ports
    (⟨none,d.regs,d.stacks⟩ : Cfg r s (size command + 1))
    registers.injective ports.injective ht
  have hr := extend_agree registers (fun i => d.regs (registers i)) d.regs (fun _ => rfl)
  have hi := extend_agree ports (initialStore a one M.bits width) d.stacks hstore
  have ho : Function.extend ports
      (finalStore a (SubexpQuarticNegMachine.negateWords p μ M one a) one M.bits width)
      d.stacks = Function.update d.stacks (ports 19)
        (flat (SubexpQuarticNegMachine.negateWords p μ M one a)) := by
    rw [finalStore_update,ProgramLinking.extend_update ports.injective,hi]
  refine ⟨n,rf,hn,Eval.call _ ?_⟩
  simpa only [callAt,programAt,ProgramLinking.embedCfg,ProgramLinking.relocatePc,
    id_eq,hr,hi,ho,StructuredProgram.State.withPC] using hl

end SubexponentialSAT.SubexpQuarticFlatNeg

end OAI.Algorithms
