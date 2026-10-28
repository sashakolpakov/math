import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramJoin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramClip
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramRead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramPrepend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramScan
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 15

structure Store where
  source : List Bool := []
  leftKey : List Bool := []
  tMaster : List Bool := []
  jMaster : List Bool := []
  output : List Bool := []
  keyRev : List Bool := []
  coeffRev : List Bool := []
  tmp : List Bool := []
  rightKey : List Bool := []
  leftCopy : List Bool := []
  joinedRev : List Bool := []
  clipKey : List Bool := []
  tCopy : List Bool := []
  jCopy : List Bool := []
  clipTmp : List Bool := []

def tapes (s : Store) : Fin 15 → List Bool :=
  ![s.source,s.leftKey,s.tMaster,s.jMaster,s.output,s.keyRev,s.coeffRev,s.tmp,
    s.rightKey,s.leftCopy,s.joinedRev,s.clipKey,s.tCopy,s.jCopy,s.clipTmp]

def state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs,tapes s⟩

structure Environment where
  leftKey : List Bool
  tMaster : List Bool
  jMaster : List Bool

def idle (e : Environment) (source output : List Bool) : Store :=
  {source := source, leftKey := e.leftKey, tMaster := e.tMaster,
    jMaster := e.jMaster, output := output}

abbrev copy (src dst : Fin 15) : Cmd 8 15 :=
  .call (copyProgram src dst 7 (0 : Fin 8) 1)

theorem copy_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 15)
    (hsd : src ≠ dst) (hst : src ≠ 7) (htd : (7 : Fin 15) ≠ dst)
    (htmp : a.tmp = []) (hout : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.copy_run src dst 7 0 1 hsd hst htd
    (by decide) regs (tapes a) (by simpa [tapes] using htmp)
  apply Eval.call
  simpa only [state, ListRegisterProgram.Run, StructuredProgram.State.withPC, hout] using he

theorem read_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 15)
    (hsd : src ≠ dst) (bits tail : List Bool)
    (hin : tapes a src = Encoding.frame bits ++ tail)
    (hout : Function.update (Function.update (tapes a) src tail) dst
      (bits.reverse ++ tapes a dst) = tapes b) :
    Eval (Program.readFrame8 src dst) (6*bits.length+4) (state regs a)
      (state (readRegs regs 0 1 (some false)) b) := by
  simpa only [state, Program.afterFrame8, hout] using
    Program.readFrame8_eval (state regs a) src dst hsd bits tail hin

theorem transfer_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 15)
    (hsd : src ≠ dst) (hout : transferStacks src dst (tapes a) = tapes b) :
    Eval (Program.transfer8 src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [state, Program.afterTransfer8, hout] using
    Program.transfer8_eval (state regs a) src dst hsd

abbrev clear (src : Fin 15) : Cmd 8 15 :=
  .call (clearProgram src (0 : Fin 8) 1)

theorem clear_store (regs : Fin 8 → Bool) (a b : Store) (src : Fin 15)
    (hout : Function.update (tapes a) src [] = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.clear_run src (0 : Fin 8) 1 regs (tapes a)
  apply Eval.call
  simpa only [state, ListRegisterProgram.Run, StructuredProgram.State.withPC,
    clearStacks, hout] using he

abbrev peek : Cmd 8 15 := .base (.atom (.peek 0 0 1))

theorem peek_eval (regs : Fin 8 → Bool) (s : Store) :
    Eval peek 1 (state regs s) (state (readRegs regs 0 1 s.source.head?) s) :=
  .base (.atom _ _)

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def regs5 : Fin 5 → Fin 8 := Fin.castAdd 3
def regs3 : Fin 3 → Fin 8 := Fin.castAdd 5
def joinPorts : Fin 3 → Fin 15 := ![9,8,10]
def clipPorts : Fin 4 → Fin 15 := ![11,12,13,14]
def emitPorts : Fin 3 → Fin 15 := ![10,6,4]

theorem regs5_inj : Function.Injective regs5 := Fin.castAdd_injective _ _
theorem regs3_inj : Function.Injective regs3 := Fin.castAdd_injective _ _
theorem joinPorts_inj : Function.Injective joinPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [joinPorts]
theorem clipPorts_inj : Function.Injective clipPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [clipPorts]
theorem emitPorts_inj : Function.Injective emitPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [emitPorts]

abbrev join : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram Program.indexJoinProgram regs5 joinPorts)

theorem join_store {n : ℕ} (regs : Fin 8 → Bool) (s : Store) (a b : Index (Fin n))
    (ha : s.leftCopy = encodeIndex a) (hb : s.rightKey = encodeIndex b)
    (ho : s.joinedRev = []) :
    ∃ rr, Eval join (4*(a.u+b.u+a.z+b.z)+6*n+22) (state regs s)
      (state rr {s with leftCopy := [], rightKey := [], joinedRev := (encodeIndex (a.join b)).reverse}) := by
  obtain ⟨rf,ht⟩ := Program.indexJoin_trace a b (regs ∘ regs5) []
  let finish := Program.maskData rf [] [] (encodeIndex (a.join b)).reverse
  let rr := (embedState regs5 joinPorts (state regs s) finish).regs
  have hs : embedState regs5 joinPorts (state regs s)
      (Program.maskData (regs ∘ regs5) (encodeIndex a) (encodeIndex b) []) = state regs s := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj joinPorts_inj
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [Program.maskData,joinPorts,state,tapes,ha,hb,ho]
    · intros; rfl
  have hf : embedState regs5 joinPorts (state regs s) finish =
      state rr {s with leftCopy := [], rightKey := [], joinedRev := (encodeIndex (a.join b)).reverse} := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj joinPorts_inj
    · intro i; exact embedState_register regs5 joinPorts (state regs s) finish regs5_inj i
    · intro i hi; exact embedState_register_frame regs5 joinPorts (state regs s) finish i hi
    · intro i; fin_cases i <;> simp [finish,Program.maskData,joinPorts,state,tapes]
    · intro i hi
      fin_cases i <;> simp_all [joinPorts,state,tapes,Fin.exists_fin_succ]
  have he := eval_call_lifted Program.indexJoinProgram regs5 joinPorts
    (state regs s) regs5_inj joinPorts_inj ht
  simp only [List.append_nil] at he
  dsimp only [finish] at hf
  exact ⟨rr, by simpa only [join,hs,hf] using he⟩

abbrev clip : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram Program.clipIndexProgram regs5 clipPorts)

theorem clip_store {n : ℕ} (regs : Fin 8 → Bool) (s : Store) (a : Index (Fin n)) (t J : ℕ)
    (hk : s.clipKey = encodeIndex a) (ht : s.tCopy = List.replicate t true)
    (hj : s.jCopy = List.replicate J true) (hz : s.clipTmp = []) :
    ∃ time ≤ 10*(a.u+a.z)+2*(t+J)+2*n+38, ∃ rr,
      Eval clip time (state regs s)
        (state rr {s with clipKey := [], tCopy := [], jCopy := [], clipTmp := []}) ∧
      rr 4 = decide (a.Kept t J) := by
  obtain ⟨time,hbound,rf,he,hflag⟩ := Program.clipIndex_trace a t J (regs ∘ regs5)
  let finish := Program.clipState rf [] [] [] []
  let rr := (embedState regs5 clipPorts (state regs s) finish).regs
  have hs : embedState regs5 clipPorts (state regs s)
      (Program.clipState (regs ∘ regs5) (encodeIndex a) (List.replicate t true)
        (List.replicate J true) []) = state regs s := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj clipPorts_inj
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [clipPorts,state,tapes,hk,ht,hj,hz]
    · intros; rfl
  have hf : embedState regs5 clipPorts (state regs s) finish =
      state rr {s with clipKey := [], tCopy := [], jCopy := [], clipTmp := []} := by
    apply embedState_eq_of_ports _ _ _ _ _ regs5_inj clipPorts_inj
    · intro i; exact embedState_register regs5 clipPorts (state regs s) finish regs5_inj i
    · intro i hi; exact embedState_register_frame regs5 clipPorts (state regs s) finish i hi
    · intro i; fin_cases i <;> simp [finish,clipPorts,state,tapes]
    · intro i hi
      fin_cases i <;> simp_all [clipPorts,state,tapes,Fin.exists_fin_succ]
  have he' := eval_call_lifted Program.clipIndexProgram regs5 clipPorts
    (state regs s) regs5_inj clipPorts_inj he
  dsimp only [finish] at hf
  refine ⟨time,hbound,rr,by simpa only [clip,hs,hf] using he',?_⟩
  have hreg := embedState_register regs5 clipPorts (state regs s) finish regs5_inj 4
  simpa [rr,regs5,finish,Program.clipState,hflag] using hreg

abbrev emit : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram Program.prependRecordProgram regs3 emitPorts)

theorem emit_store (regs : Fin 8 → Bool) (s : Store) (key coeff : List Bool)
    (hk : s.joinedRev = key.reverse) (hc : s.coeffRev = coeff.reverse) :
    ∃ rr, Eval emit (4*key.length+4*coeff.length+13) (state regs s)
      (state rr {s with joinedRev := [], coeffRev := [], output := Encoding.frame key ++ Encoding.frame coeff ++ s.output}) := by
  obtain ⟨rf,ht⟩ := Program.prependRecord_trace (regs ∘ regs3) key coeff s.output
  let finish := Program.prependData rf [] [] (Encoding.frame key ++ Encoding.frame coeff ++ s.output)
  let rr := (embedState regs3 emitPorts (state regs s) finish).regs
  have hs : embedState regs3 emitPorts (state regs s)
      (Program.prependData (regs ∘ regs3) key.reverse coeff.reverse s.output) = state regs s := by
    apply embedState_eq_of_ports _ _ _ _ _ regs3_inj emitPorts_inj
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [Program.prependData,emitPorts,state,tapes,hk,hc]
    · intros; rfl
  have hf : embedState regs3 emitPorts (state regs s) finish =
      state rr {s with joinedRev := [], coeffRev := [], output := Encoding.frame key ++ Encoding.frame coeff ++ s.output} := by
    apply embedState_eq_of_ports _ _ _ _ _ regs3_inj emitPorts_inj
    · intro i; exact embedState_register regs3 emitPorts (state regs s) finish regs3_inj i
    · intro i hi; exact embedState_register_frame regs3 emitPorts (state regs s) finish i hi
    · intro i; fin_cases i <;> simp [finish,Program.prependData,emitPorts,state,tapes]
    · intro i hi
      fin_cases i <;> simp_all [emitPorts,state,tapes,Fin.exists_fin_succ]
  have he := eval_call_lifted Program.prependRecordProgram regs3 emitPorts
    (state regs s) regs3_inj emitPorts_inj ht
  dsimp only [finish] at hf
  exact ⟨rr,by simpa only [emit,hs,hf] using he⟩

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev prepare : Cmd 8 15 :=
  .seq (Program.readFrame8 0 5) (.seq (Program.readFrame8 0 6)
    (.seq (Program.transfer8 5 8) (copy 1 9)))

def prepared (e : Environment) (key coeff tail output : List Bool) : Store :=
  {idle e tail output with rightKey := key, leftCopy := e.leftKey, coeffRev := coeff.reverse}

theorem prepare_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail output : List Bool) :
    ∃ rr, Eval prepare (9*key.length+6*coeff.length+7*e.leftKey.length+16)
      (state regs (idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) output))
      (state rr (prepared e key coeff tail output)) := by
  let a := idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) output
  let b := {a with source := Encoding.frame coeff ++ tail, keyRev := key.reverse}
  let c := {b with source := tail, coeffRev := coeff.reverse}
  let d := {c with keyRev := [], rightKey := key}
  let f := prepared e key coeff tail output
  let r1 := readRegs regs 0 1 (some false)
  let r2 := readRegs r1 0 1 (some false)
  let r3 := readRegs r2 0 1 none
  have h1 := read_store regs a b 0 5 (by decide) key (Encoding.frame coeff ++ tail)
    (by simp [a,idle,tapes,List.append_assoc])
    (by funext i; fin_cases i <;> simp [a,b,idle,tapes])
  have h2 := read_store r1 b c 0 6 (by decide) coeff tail rfl
    (by funext i; fin_cases i <;> simp [a,b,c,idle,tapes])
  have h3 := transfer_store r2 c d 5 8 (by decide)
    (by funext i; fin_cases i <;> simp [a,b,c,d,idle,tapes,transferStacks])
  have h4 := copy_store r3 d f 1 9 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,c,d,f,prepared,idle,tapes,copyStacks])
  have he := h1.seq (h2.seq (h3.seq h4))
  refine ⟨readRegs r3 0 1 none,?_⟩
  convert he using 1 ;
    simp [a,b,c,d,idle,tapes] ; omega

def joined (e : Environment) (key coeff tail output : List Bool) : Store :=
  {idle e tail output with joinedRev := key.reverse, coeffRev := coeff.reverse}

abbrev prepareClip : Cmd 8 15 :=
  .seq (copy 10 5) (.seq (Program.transfer8 5 11) (.seq (copy 2 12) (copy 3 13)))

def clipReady (e : Environment) (key coeff tail output : List Bool) : Store :=
  {joined e key coeff tail output with clipKey := key, tCopy := e.tMaster, jCopy := e.jMaster}

theorem prepareClip_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail output : List Bool) :
    ∃ rr, Eval prepareClip
      (10*key.length+7*e.tMaster.length+7*e.jMaster.length+18)
      (state regs (joined e key coeff tail output))
      (state rr (clipReady e key coeff tail output)) := by
  let a := joined e key coeff tail output
  let b := {a with keyRev := key.reverse}
  let c := {b with keyRev := [], clipKey := key}
  let d := {c with tCopy := e.tMaster}
  let f := clipReady e key coeff tail output
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  have h1 := copy_store regs a b 10 5 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,joined,idle,tapes,copyStacks])
  have h2 := transfer_store r1 b c 5 11 (by decide)
    (by funext i; fin_cases i <;> simp [a,b,c,joined,idle,tapes,transferStacks])
  have h3 := copy_store r2 c d 2 12 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,c,d,joined,idle,tapes,copyStacks])
  have h4 := copy_store r3 d f 3 13 (by decide) (by decide) (by decide) rfl
    (by funext i; fin_cases i <;> simp [a,b,c,d,f,clipReady,joined,idle,tapes,copyStacks])
  have he := h1.seq (h2.seq (h3.seq h4))
  refine ⟨readRegs r3 0 1 none,?_⟩
  convert he using 1 ;
    simp [a,b,c,d,joined,idle,tapes] ; omega

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finish : Cmd 8 15 := .ite 4 emit (.seq (clear 10) (clear 6))

theorem finish_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail output : List Bool) (flag : Bool) (hf : regs 4 = flag) :
    ∃ time ≤ 4*key.length+4*coeff.length+14, ∃ rr,
      Eval finish time (state regs (joined e key coeff tail output))
        (state rr (idle e tail
          (if flag then Encoding.frame key ++ Encoding.frame coeff ++ output else output))) := by
  cases flag with
  | true =>
    obtain ⟨rr,he⟩ := emit_store regs (joined e key coeff tail output) key coeff rfl rfl
    refine ⟨(4*key.length+4*coeff.length+13)+1,by omega,rr,?_⟩
    have ht := Eval.ite_true (no := .seq (clear 10) (clear 6)) (by simpa [state] using hf) he
    simpa [finish,joined,idle] using ht
  | false =>
    let a := joined e key coeff tail output
    let b := {a with joinedRev := []}
    have h1 := clear_store regs a b 10
      (by funext i; fin_cases i <;> simp [a,b,joined,idle,tapes])
    have h2 := clear_store (readRegs regs 0 1 none) b (idle e tail output) 6
      (by funext i; fin_cases i <;> simp [a,b,joined,idle,tapes])
    refine ⟨(2*key.length+3)+(2*coeff.length+3)+1,?_,
      readRegs (readRegs regs 0 1 none) 0 1 none,?_⟩
    · simp []
      omega
    · have ht := Eval.ite_false (yes := emit) (by simpa [state] using hf) (h1.seq h2)
      simpa [finish,a,b,joined,idle,tapes] using ht

def environment {n : ℕ} (a : Index (Fin n)) (t J : ℕ) : Environment :=
  ⟨encodeIndex a,List.replicate t true,List.replicate J true⟩

abbrev step : Cmd 8 15 := .seq prepare (.seq join (.seq prepareClip (.seq clip finish)))

def stepBudget {n : ℕ} (a b : Index (Fin n)) (t J coeffLength : ℕ) : ℕ :=
  9*(encodeIndex b).length+10*coeffLength+7*(encodeIndex a).length+
    14*(encodeIndex (a.join b)).length+14*(a.u+b.u+a.z+b.z)+8*n+9*(t+J)+108

theorem step_eval {n : ℕ} (regs : Fin 8 → Bool) (a b : Index (Fin n)) (t J : ℕ)
    (coeff tail output : List Bool) :
    ∃ time ≤ stepBudget a b t J coeff.length, ∃ rr,
      Eval step time
        (state regs (idle (environment a t J)
          (Encoding.frame (encodeIndex b) ++ Encoding.frame coeff ++ tail) output))
        (state rr (idle (environment a t J) tail
          (if (a.join b).Kept t J then
            Encoding.frame (encodeIndex (a.join b)) ++ Encoding.frame coeff ++ output
          else output))) := by
  let e := environment a t J
  obtain ⟨r1,h1⟩ := prepare_eval regs e (encodeIndex b) coeff tail output
  obtain ⟨r2,h2⟩ := join_store r1 (prepared e (encodeIndex b) coeff tail output) a b rfl rfl rfl
  have h2' : Eval join (4*(a.u+b.u+a.z+b.z)+6*n+22)
      (state r1 (prepared e (encodeIndex b) coeff tail output))
      (state r2 (joined e (encodeIndex (a.join b)) coeff tail output)) := by
    simpa [prepared,joined,idle] using h2
  obtain ⟨r3,h3⟩ := prepareClip_eval r2 e (encodeIndex (a.join b)) coeff tail output
  obtain ⟨c,hc,r4,h4,hflag⟩ := clip_store r3
    (clipReady e (encodeIndex (a.join b)) coeff tail output) (a.join b) t J rfl rfl rfl rfl
  have h4' : Eval clip c
      (state r3 (clipReady e (encodeIndex (a.join b)) coeff tail output))
      (state r4 (joined e (encodeIndex (a.join b)) coeff tail output)) := by
    simpa [clipReady,joined,idle] using h4
  obtain ⟨f,hf,r5,h5⟩ := finish_eval r4 e (encodeIndex (a.join b)) coeff tail output
    (decide ((a.join b).Kept t J)) hflag
  refine ⟨_,?_,r5,by simpa [step] using h1.seq (h2'.seq (h3.seq (h4'.seq h5)))⟩
  simp only [stepBudget,e,environment,List.length_replicate,encodeIndex_length,Index.join] at hc hf ⊢
  omega

theorem stepBudget_bound {n : ℕ} (a b : Index (Fin n)) (t J C : ℕ)
    (ha : a.Kept t J) (hb : b.Kept t J) :
    stepBudget a b t J C ≤ 100*(n+t+J+C+2) := by
  obtain ⟨hau,haz⟩ := ha
  obtain ⟨hbu,hbz⟩ := hb
  simp only [stepBudget,encodeIndex_length,Index.join]
  omega

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Entry (n : ℕ) := Index (Fin n) × List Bool

def encoded {n : ℕ} (entries : List (Entry n)) : List Program.ByteRecord :=
  entries.map (fun b => (encodeIndex b.1,b.2))

abbrev mapped {n : ℕ} (a : Index (Fin n)) (t J : ℕ) : List (Entry n) → List (Entry n)
  | [] => []
  | (b,c) :: rest => if (a.join b).Kept t J then (a.join b,c) :: mapped a t J rest
      else mapped a t J rest

abbrev accumulated {n : ℕ} (a : Index (Fin n)) (t J : ℕ) :
    List (Entry n) → List Bool → List Bool
  | [], output => output
  | (b,c) :: rest, output => accumulated a t J rest
      (if (a.join b).Kept t J then
        Encoding.frame (encodeIndex (a.join b)) ++ Encoding.frame c ++ output else output)

abbrev loop : Cmd 8 15 := .while 1 (.seq step peek)
abbrev scan : Cmd 8 15 := .seq peek loop

def ready {n : ℕ} (regs : Fin 8 → Bool) (a : Index (Fin n)) (t J : ℕ)
    (entries : List (Entry n)) (output : List Bool) : Data :=
  state (readRegs regs 0 1 (Program.rawEntries (encoded entries)).head?)
    (idle (environment a t J) (Program.rawEntries (encoded entries)) output)

def budget {n : ℕ} (a : Index (Fin n)) (t J : ℕ) : List (Entry n) → ℕ
  | [] => 1
  | (b,c) :: rest => stepBudget a b t J c.length + 2 + budget a t J rest

theorem ready_nil_guard {n : ℕ} (regs : Fin 8 → Bool) (a : Index (Fin n))
    (t J : ℕ) (output : List Bool) : (ready regs a t J [] output).regs 1 = false := by
  simp [ready,encoded,Program.rawEntries,state,readRegs]

theorem ready_cons_guard {n : ℕ} (regs : Fin 8 → Bool) (a b : Index (Fin n))
    (t J : ℕ) (c : List Bool) (rest : List (Entry n)) (output : List Bool) :
    (ready regs a t J ((b,c)::rest) output).regs 1 = true := by
  cases h : encodeIndex b <;>
    simp [ready,encoded,Program.rawEntries,state,readRegs,Encoding.frame,h]

theorem loop_eval {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (entries : List (Entry n))
    (output : List Bool) (regs : Fin 8 → Bool) :
    ∃ time ≤ budget a t J entries, ∃ rr,
      Eval loop time (ready regs a t J entries output)
        (state rr (idle (environment a t J) [] (accumulated a t J entries output))) := by
  induction entries generalizing output regs with
  | nil =>
    refine ⟨1,le_rfl,readRegs regs 0 1 none,?_⟩
    exact Eval.while_false (ready_nil_guard regs a t J output)
  | cons entry entries ih =>
    rcases entry with ⟨b,c⟩
    let rg := readRegs regs 0 1 (Program.rawEntries (encoded ((b,c)::entries))).head?
    let out := if (a.join b).Kept t J then
      Encoding.frame (encodeIndex (a.join b)) ++ Encoding.frame c ++ output else output
    obtain ⟨s,hs,middle,he⟩ := step_eval rg a b t J c (Program.rawEntries (encoded entries)) output
    obtain ⟨v,hv,rr,ht⟩ := ih out middle
    have hp := peek_eval middle (idle (environment a t J) (Program.rawEntries (encoded entries)) out)
    refine ⟨s+1+v+1,?_,rr,?_⟩
    · simp only [budget]
      omega
    · have hh := Eval.while_true (ready_cons_guard regs a b t J c entries output) (he.seq hp) ht
      exact hh

theorem accumulated_eq {n : ℕ} (a : Index (Fin n)) (t J : ℕ)
    (entries : List (Entry n)) (output : List Bool) :
    accumulated a t J entries output =
      Program.rawEntries (encoded (mapped a t J entries).reverse) ++ output := by
  induction entries generalizing output with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨b,c⟩
    by_cases hk : (a.join b).Kept t J <;>
      simp [accumulated,mapped,hk,ih,encoded,List.reverse_cons,Program.rawEntries_append,
        Program.rawEntries,List.append_assoc]

theorem scan_eval {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (entries : List (Entry n))
    (output : List Bool) (regs : Fin 8 → Bool) :
    ∃ time ≤ budget a t J entries + 1, ∃ rr,
      Eval scan time
        (state regs (idle (environment a t J) (Program.rawEntries (encoded entries)) output))
        (state rr (idle (environment a t J) []
          (Program.rawEntries (encoded (mapped a t J entries).reverse) ++ output))) := by
  obtain ⟨time,ht,rr,he⟩ := loop_eval a t J entries output regs
  rw [accumulated_eq] at he
  refine ⟨1+time,by omega,rr,?_⟩
  exact (peek_eval regs _).seq he

def scanProgram := compiled scan 0 4

theorem scan_trace {n : ℕ} (a : Index (Fin n)) (t J : ℕ) (entries : List (Entry n))
    (output : List Bool) (regs : Fin 8 → Bool) :
    ∃ time ≤ budget a t J entries + 2, ∃ rr,
      Trace scanProgram time
        ((state regs (idle (environment a t J) (Program.rawEntries (encoded entries)) output)).withPC
          (some scanProgram.entry))
        ((state rr (idle (environment a t J) []
          (Program.rawEntries (encoded (mapped a t J entries).reverse) ++ output))).withPC none) := by
  obtain ⟨time,ht,rr,he⟩ := scan_eval a t J entries output regs
  exact ⟨time+1,by omega,rr,compiled_halt_trace he 0 4⟩

theorem budget_bound {n : ℕ} (a : Index (Fin n)) (t J C : ℕ) (entries : List (Entry n))
    (ha : a.Kept t J) (hb : ∀ b ∈ entries, b.1.Kept t J)
    (hc : ∀ b ∈ entries, b.2.length ≤ C) :
    budget a t J entries ≤ entries.length * (100*(n+t+J+C+2)+2)+1 := by
  induction entries with
  | nil => simp [budget]
  | cons b entries ih =>
    have hs := stepBudget_bound a b.1 t J b.2.length ha (hb b (by simp))
    have hbc := hc b (by simp)
    have ht := ih (fun b h => hb b (by simp [h])) (fun b h => hc b (by simp [h]))
    cases b
    simp only [budget,List.length_cons] at *
    nlinarith

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem mapped_eq_filter_map {n : ℕ} (a : Index (Fin n)) (t J : ℕ)
    (entries : List (Entry n)) :
    mapped a t J entries =
      (entries.filter (fun b => decide ((a.join b.1).Kept t J))).map
        (fun b => (a.join b.1,b.2)) := by
  induction entries with
  | nil => rfl
  | cons b entries ih =>
    cases b with
    | mk b c =>
      by_cases hk : (a.join b).Kept t J <;> simp [mapped,hk,ih]

theorem mapped_length_le {n : ℕ} (a : Index (Fin n)) (t J : ℕ)
    (entries : List (Entry n)) : (mapped a t J entries).length ≤ entries.length := by
  rw [mapped_eq_filter_map,List.length_map]
  exact List.length_filter_le _ _

theorem mapped_kept {n : ℕ} (a : Index (Fin n)) (t J : ℕ)
    (entries : List (Entry n)) : ∀ b ∈ mapped a t J entries, b.1.Kept t J := by
  rw [mapped_eq_filter_map]
  intro b hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  exact of_decide_eq_true (List.mem_filter.mp hc).2

/-- The final trace has a linear dictionary-length bound, and preserves the
three caller-owned masters. All ten scratch stacks are empty on return. -/
theorem native_map_trace {n : ℕ} (a : Index (Fin n)) (t J C : ℕ)
    (entries : List (Entry n)) (regs : Fin 8 → Bool) (output : List Bool)
    (ha : a.Kept t J) (hb : ∀ b ∈ entries, b.1.Kept t J)
    (hc : ∀ b ∈ entries, b.2.length ≤ C) :
    ∃ time ≤ entries.length*(100*(n+t+J+C+2)+2)+3, ∃ rr,
      Trace scanProgram time
        ((state regs (idle (environment a t J) (Program.rawEntries (encoded entries)) output)).withPC
          (some scanProgram.entry))
        ((state rr (idle (environment a t J) []
          (Program.rawEntries (encoded (mapped a t J entries).reverse) ++ output))).withPC none) := by
  obtain ⟨time,ht,rr,he⟩ := scan_trace a t J entries output regs
  exact ⟨time,by have h := budget_bound a t J C entries ha hb hc; omega,rr,he⟩

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

#print axioms SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.native_map_trace
#print axioms SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.mapped_eq_filter_map

end OAI.Algorithms
