import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.SymbolicCost

namespace OAI.Algorithms

/-! Indexed access to the current exponent vector uses the actual unary field
encoding. Both the vector and the requested index remain data, not control. -/

namespace SubexponentialSAT.SubexpExponentGather

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 3 7

def words (ns : List ℕ) : List Bool := ns.flatMap Encoding.encodeNat

theorem words_eq (ns : List ℕ) : words ns = SymbolicCost.unaryWords ns := rfl

def st (regs : Fin 3 → Bool) (master source index value tmp output scratch : List Bool) : Data :=
  ⟨regs,![master,source,index,value,tmp,output,scratch]⟩

/-- Stack 1 is the copied vector and stack 2 is a unary index. -/
abbrev skipProgram : Program 3 7 5 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code := ![.pop 2 0 1 1,.branch 1 2 4,.pop 1 0 1 3,.branch 0 2 0,.halt]

theorem skip_field_trace (n : ℕ) (rest : List Bool) (regs : Fin 3 → Bool)
    (stk : Fin 7 → List Bool) (hs : stk 1 = Encoding.encodeNat n ++ rest) :
    Trace skipProgram (2*n+2) ⟨some 2,regs,stk⟩
      ⟨some 0,readRegs regs 0 1 (some false),Function.update stk 1 rest⟩ := by
  induction n generalizing regs stk with
  | zero =>
      have hh : stk 1 = false::rest := by simpa [Encoding.encodeNat] using hs
      refine .cons (b := ⟨some 3,readRegs regs 0 1 (some false),Function.update stk 1 rest⟩) ?_ ?_
      · simp [step,execInstr,hh]
      · refine .cons (b := ⟨some 0,readRegs regs 0 1 (some false),Function.update stk 1 rest⟩) ?_ (.refl _)
        simp [step,execInstr,readRegs]
  | succ n ih =>
      let rr := readRegs regs 0 1 (some true)
      let ss := Function.update stk 1 (Encoding.encodeNat n++rest)
      have hh : stk 1 = true::(Encoding.encodeNat n++rest) := by
        simpa [Encoding.encodeNat,List.replicate_succ] using hs
      have hi := ih rr ss (by simp [ss])
      have hr : readRegs rr 0 1 (some false) = readRegs regs 0 1 (some false) := by
        funext j; fin_cases j <;> simp [rr,readRegs]
      have hi' : Trace skipProgram (2*n+2) ⟨some 2,rr,ss⟩
          ⟨some 0,readRegs regs 0 1 (some false),Function.update stk 1 rest⟩ := by
        simpa [ss,hr] using hi
      have ht : Trace skipProgram (2*n+2+2) ⟨some 2,regs,stk⟩
          ⟨some 0,readRegs regs 0 1 (some false),Function.update stk 1 rest⟩ := by
        refine .cons (b := ⟨some 3,rr,ss⟩) ?_ ?_
        · simp [step,execInstr,hh,rr,ss]
        · refine .cons (b := ⟨some 2,rr,ss⟩) ?_ hi'
          simp [step,execInstr,rr,readRegs]
      convert ht using 1

def skipCost (ns : List ℕ) : ℕ := (ns.map (fun n => 2*n+4)).sum

def skipStacks (rest : List Bool) (stk : Fin 7 → List Bool) : Fin 7 → List Bool :=
  Function.update (Function.update stk 1 rest) 2 []

theorem skip_trace (ns : List ℕ) (rest : List Bool) (regs : Fin 3 → Bool)
    (stk : Fin 7 → List Bool) (hs : stk 1 = words ns ++ rest)
    (hi : stk 2 = List.replicate ns.length true) :
    Trace skipProgram (skipCost ns+2) ⟨some 0,regs,stk⟩
      ⟨some 4,readRegs regs 0 1 none,skipStacks rest stk⟩ := by
  induction ns generalizing regs stk with
  | nil =>
      have he : skipStacks rest stk = Function.update stk 2 [] := by
        have hh : stk 1 = rest := by simpa [words] using hs
        simp [skipStacks,←hh]
      refine .cons (b := ⟨some 1,readRegs regs 0 1 none,Function.update stk 2 []⟩) ?_ ?_
      · simp [step,execInstr,hi]
      · refine .cons (b := ⟨some 4,readRegs regs 0 1 none,skipStacks rest stk⟩) ?_ (.refl _)
        simp [step,execInstr,readRegs,he]
  | cons n ns ih =>
      let rr := readRegs regs 0 1 (some true)
      let ss := Function.update stk 2 (List.replicate ns.length true)
      have hh : ss 1 = Encoding.encodeNat n++(words ns++rest) := by
        simpa [ss,words,List.append_assoc] using hs
      have hf := skip_field_trace n (words ns++rest) rr ss hh
      let rr' := readRegs rr 0 1 (some false)
      let ss' := Function.update ss 1 (words ns++rest)
      have ht := ih rr' ss' (by simp [ss']) (by simp [ss',ss])
      have he : skipStacks rest ss' = skipStacks rest stk := by
        funext i; fin_cases i <;> simp [skipStacks,ss',ss]
      have ht' : Trace skipProgram (skipCost ns+2) ⟨some 0,rr',ss'⟩
          ⟨some 4,readRegs regs 0 1 none,skipStacks rest stk⟩ := by
        simpa [rr',rr,he,StackRoutines.readRegs_reset] using ht
      have first : Trace skipProgram 2 ⟨some 0,regs,stk⟩ ⟨some 2,rr,ss⟩ := by
        refine .cons (b := ⟨some 1,rr,ss⟩) ?_ ?_
        · simp [step,execInstr,hi,List.replicate_succ,rr,ss]
        · refine .cons (b := ⟨some 2,rr,ss⟩) ?_ (.refl _)
          simp [step,execInstr,rr,readRegs]
      have all := (first.trans hf).trans ht'
      convert all using 1
      simp [skipCost]
      omega

theorem skip_eval (ns : List ℕ) (rest : List Bool) (d : Data)
    (hs : d.stacks 1 = words ns++rest) (hi : d.stacks 2 = List.replicate ns.length true) :
    Eval (.call skipProgram) (skipCost ns+3) d
      ⟨readRegs d.regs 0 1 none,skipStacks rest d.stacks⟩ := by
  have h := skip_trace ns rest d.regs d.stacks hs hi
  have hh := StackRoutines.halt_after_trace skipProgram h 4 rfl rfl
  apply Eval.call
  simpa [skipProgram,StructuredProgram.State.withPC,Nat.add_assoc] using hh

def readRegsMap : Fin 2 → Fin 3 := Fin.castAdd 1
def readPorts : Fin 2 → Fin 7 := ![1,3]
theorem readRegsMap_injective : Function.Injective readRegsMap := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 3 => x.val) h
theorem readPorts_injective : Function.Injective readPorts := by decide

def readProgram := ProgramLinking.liftProgram ParserProgram.natProgram readRegsMap readPorts

theorem read_eval (regs : Fin 3 → Bool) (master index tmp output scratch : List Bool)
    (n : ℕ) (rest : List Bool) :
    Eval (.call readProgram) (4*n+4)
      (st regs master (Encoding.encodeNat n++rest) index [] tmp output scratch)
      (st (readRegs regs 0 1 (some false)) master rest index (List.replicate n true) tmp output scratch) := by
  let d := st regs master (Encoding.encodeNat n++rest) index [] tmp output scratch
  let a : State 2 2 := ⟨ParserProgram.pair (regs 0) (regs 1),
    ParserProgram.pair (Encoding.encodeNat n++rest) []⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (List.replicate n true++[])⟩
  have ha : embedState readRegsMap readPorts d a = d := by
    apply embedState_eq _ _ readRegsMap_injective readPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState readRegsMap readPorts d b =
      st (readRegs regs 0 1 (some false)) master rest index (List.replicate n true) tmp output scratch := by
    apply embedState_eq _ _ readRegsMap_injective readPorts_injective
    · intro i; fin_cases i <;> simp [st,readRegsMap,readRegs,b,ParserProgram.pair]
    · intro i; fin_cases i <;> simp [st,readPorts,b,ParserProgram.pair]
    · intro j hj
      fin_cases j
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
      · rfl
    · intro j hj
      fin_cases j <;> try rfl
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
  have h := eval_call_lifted ParserProgram.natProgram readRegsMap readPorts d
    readRegsMap_injective readPorts_injective (a := a) (b := b)
    (ParserProgram.nat_trace n rest [] (regs 0) (regs 1))
  simpa only [readProgram,ha,hb] using h

def countPorts : Fin 3 → Fin 7 := ![3,5,6]
theorem countPorts_injective : Function.Injective countPorts := by decide
def countProgram := ProgramLinking.liftProgram CounterPrograms.lengthProgram id countPorts

theorem count_eval (regs : Fin 3 → Bool) (master source index value tmp : List Bool)
    (hz : regs 2 = false) :
    ∃ n ≤ value.length*(8*value.length+10)+3, ∃ output,
      Eval (.call countProgram) n
        (st regs master source index value tmp [] [])
        (st (fun _ => false) master source index [] tmp output []) ∧
      BinaryArithmetic.toNat output = value.length ∧ output.length ≤ value.length := by
  obtain ⟨output,hvalue,hlen,n,hn,ht⟩ := CounterPrograms.length_correct_from (regs 0) (regs 1) value
  let d := st regs master source index value tmp [] []
  let a : State 3 3 := ⟨CounterPrograms.counterRegs (regs 0) (regs 1) false,
    CounterPrograms.lengthStacks value [] []⟩
  let b : State 3 3 := ⟨fun _ => false,CounterPrograms.lengthStacks [] output []⟩
  have ha : embedState id countPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id countPorts_injective
    · intro i; fin_cases i <;> simp [d,st,a,CounterPrograms.counterRegs,hz]
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intros; rfl
  have hb : embedState id countPorts d b = st (fun _ => false) master source index [] tmp output [] := by
    apply embedState_eq _ _ Function.injective_id countPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      fin_cases j <;> try rfl
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
  have hend : terminal CounterPrograms.lengthProgram output = b.withPC none := by
    dsimp [terminal,b,StructuredProgram.State.withPC]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hstart : a.withPC (some CounterPrograms.lengthProgram.entry) =
      CounterPrograms.lengthCfg 0 (regs 0) (regs 1) false value [] [] := by
    rfl
  have htrace : Trace CounterPrograms.lengthProgram n
      (a.withPC (some CounterPrograms.lengthProgram.entry)) (b.withPC none) := by
    simpa only [hstart, hend] using ht
  have h := eval_call_lifted CounterPrograms.lengthProgram id countPorts d
    Function.injective_id countPorts_injective htrace
  exact ⟨n,hn,output,by simpa only [ha,hb,countProgram] using h,
    (CounterPrograms.value_eq_toNat output).symm.trans hvalue,hlen⟩

abbrev gather : Cmd 3 7 :=
  .seq (.call (StackRoutines.copyProgram 0 1 4 (0 : Fin 3) 1))
    (.seq (.call skipProgram)
      (.seq (.call readProgram)
        (.seq (.call (StackRoutines.clearProgram 1 (0 : Fin 3) 1))
          (.seq (.base (.atom (.set 2 false))) (.call countProgram)))))

def gatherBudget (beforeFields : List ℕ) (n : ℕ) (suffix : List ℕ) : ℕ :=
  7*(words (beforeFields++n::suffix)).length + skipCost beforeFields + 4*n +
    2*(words suffix).length + n*(8*n+10)+19

theorem gather_eval (regs : Fin 3 → Bool) (beforeFields : List ℕ) (n : ℕ) (suffix : List ℕ) :
    ∃ t ≤ gatherBudget beforeFields n suffix, ∃ output,
      Eval gather t
        (st regs (words (beforeFields++n::suffix)) [] (List.replicate beforeFields.length true) [] [] [] [])
        (st (fun _ => false) (words (beforeFields++n::suffix)) [] [] [] [] output []) ∧
      BinaryArithmetic.toNat output = n ∧ output.length ≤ n := by
  let master := words (beforeFields++n::suffix)
  let r₁ := readRegs regs 0 1 none
  let d := st regs master [] (List.replicate beforeFields.length true) [] [] [] []
  have hc := copy_eval d 0 1 4 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hec : afterCopy d 0 1 0 1 = st r₁ master master (List.replicate beforeFields.length true) [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterCopy,d,st,StackRoutines.copyStacks]
  rw [hec] at hc
  have hs := skip_eval beforeFields (Encoding.encodeNat n++words suffix)
    (st r₁ master master (List.replicate beforeFields.length true) [] [] [] [])
    (by simp [st,master,words,List.flatMap_append]) rfl
  have hes : (⟨readRegs (st r₁ master master (List.replicate beforeFields.length true) [] [] [] []).regs
      0 1 none,skipStacks (Encoding.encodeNat n++words suffix)
      (st r₁ master master (List.replicate beforeFields.length true) [] [] [] []).stacks⟩ : Data) =
      st r₁ master (Encoding.encodeNat n++words suffix) [] [] [] [] [] := by
    apply state_ext
    · simp [st,r₁,StackRoutines.readRegs_reset]
    · funext i; fin_cases i <;> simp [skipStacks,st]
  rw [hes] at hs
  have hr := read_eval r₁ master [] [] [] [] n (words suffix)
  let r₂ := readRegs r₁ 0 1 (some false)
  let beforeClear := st r₂ master (words suffix) [] (List.replicate n true) [] [] []
  have hcl : Eval (.call (StackRoutines.clearProgram 1 (0 : Fin 3) 1))
      (2*(words suffix).length+3) beforeClear
      (st r₁ master [] [] (List.replicate n true) [] [] []) := by
    apply Eval.call
    have h := StackRoutines.clearProgram_trace 1 (0 : Fin 3) 1 beforeClear.regs beforeClear.stacks
    have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
    have hstacks : StackRoutines.clearStacks 1 beforeClear.stacks =
        (st r₁ master [] [] (List.replicate n true) [] [] []).stacks := by
      funext j; fin_cases j <;> simp [StackRoutines.clearStacks,beforeClear,st]
    simp only [StackRoutines.clearResult] at hh
    rw [hstacks] at hh
    simpa [beforeClear,st,StackRoutines.clearProgram,StackRoutines.clearResult,
      r₂,r₁,StackRoutines.readRegs_reset,
      StructuredProgram.State.withPC,Nat.add_assoc] using hh
  let r₃ := Function.update r₁ 2 false
  have hz : Eval (.base (.atom (.set 2 false))) 1
      (st r₁ master [] [] (List.replicate n true) [] [] [])
      (st r₃ master [] [] (List.replicate n true) [] [] []) :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  obtain ⟨k,hk,output,hkRun,hvalue,hlen⟩ := count_eval r₃ master [] [] (List.replicate n true) [] (by simp [r₃])
  simp only [List.length_replicate] at hk hvalue hlen
  refine ⟨(7*master.length+5)+(skipCost beforeFields+3+(4*n+4+
    (2*(words suffix).length+3+(1+k)))),?_,output,?_,hvalue,hlen⟩
  · unfold gatherBudget
    dsimp [master] at *
    omega
  · exact Eval.seq hc (Eval.seq hs (Eval.seq hr (Eval.seq hcl (Eval.seq hz hkRun))))

abbrev program : Program 3 7 (StructuredCalls.size gather+1) := StructuredCalls.compiled gather 0 5

theorem control_size : StructuredCalls.size gather = 36 := by decide

theorem gather_runs (regs : Fin 3 → Bool) (beforeFields : List ℕ) (n : ℕ) (suffix : List ℕ) :
    ∃ output, RunsIn program (gatherBudget beforeFields n suffix+1)
      ((st regs (words (beforeFields++n::suffix)) [] (List.replicate beforeFields.length true) [] [] [] []).withPC
        (some program.entry))
      ((st (fun _ => false) (words (beforeFields++n::suffix)) [] [] [] [] output []).withPC none) ∧
      BinaryArithmetic.toNat output = n ∧ output.length ≤ n := by
  obtain ⟨t,ht,out,hr,hv,hl⟩ := gather_eval regs beforeFields n suffix
  exact ⟨out,⟨t+1,by omega,StructuredCalls.compiled_halt_trace hr 0 5⟩,hv,hl⟩

theorem ofFn_decomposition {D : ℕ} {A : Type*} (a : Fin D → A) (i : Fin D) :
    List.ofFn a = (List.ofFn a).take i.val ++ a i :: (List.ofFn a).drop (i.val+1) := by
  have hi : i.val < (List.ofFn a).length := by simp [i.isLt]
  have h := List.take_append_drop i.val (List.ofFn a)
  rw [List.drop_eq_getElem_cons hi] at h
  simpa using h.symm

theorem ofFn_prefix_length {D : ℕ} {A : Type*} (a : Fin D → A) (i : Fin D) :
    ((List.ofFn a).take i.val).length = i.val := by
  simp [List.length_take]

theorem gather_index_runs {D : ℕ} (regs : Fin 3 → Bool) (a : Fin D → ℕ) (i : Fin D) :
    ∃ output, RunsIn program
      (gatherBudget ((List.ofFn a).take i.val) (a i) ((List.ofFn a).drop (i.val+1))+1)
      ((st regs (SymbolicCost.unaryWords (List.ofFn a)) [] (List.replicate i.val true)
        [] [] [] []).withPC (some program.entry))
      ((st (fun _ => false) (SymbolicCost.unaryWords (List.ofFn a)) [] [] [] [] output []).withPC none) ∧
      BinaryArithmetic.toNat output = a i ∧ output.length ≤ a i := by
  have h := gather_runs regs ((List.ofFn a).take i.val) (a i) ((List.ofFn a).drop (i.val+1))
  simpa only [←ofFn_decomposition a i,ofFn_prefix_length,words_eq] using h

theorem gather_primitive_runs (regs : Fin 3 → Bool) (beforeFields : List ℕ) (n : ℕ) (suffix : List ℕ) :
    ∃ output, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program*(gatherBudget beforeFields n suffix+1))
      (BitProgram.primitiveCfg program
        ((st regs (words (beforeFields++n::suffix)) [] (List.replicate beforeFields.length true) [] [] [] []).withPC
          (some program.entry)))
      (BitProgram.primitiveCfg program
        ((st (fun _ => false) (words (beforeFields++n::suffix)) [] [] [] [] output []).withPC none)) ∧
      BinaryArithmetic.toNat output = n ∧ output.length ≤ n := by
  obtain ⟨out,hr,hv,hl⟩ := gather_runs regs beforeFields n suffix
  exact ⟨out,BitProgram.primitive_execution program hr,hv,hl⟩

end SubexponentialSAT.SubexpExponentGather

end OAI.Algorithms
