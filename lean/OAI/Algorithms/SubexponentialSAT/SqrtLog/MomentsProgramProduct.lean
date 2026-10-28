import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeScaleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeKeyMapProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramNormalize

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 56

def scalePorts : Fin 40 → Fin 56 := Fin.castAdd 16

def keyPorts : Fin 15 → Fin 56 := ![0,1,2,3,4,6,7,8,9,10,11,13,14,15,16]

def normalizePorts (i : Fin 28) : Fin 56 :=
  if i = 15 then 42 else if i = 17 then 49 else if i = 22 then 50 else
  if i = 24 then 51 else Fin.castAdd 28 i

theorem scalePorts_injective : Function.Injective scalePorts := Fin.castAdd_injective _ _
theorem keyPorts_injective : Function.Injective keyPorts := by decide
theorem normalizePorts_injective : Function.Injective normalizePorts := by decide

abbrev copy (src dst : Fin 56) : Cmd 8 56 := .call (copyProgram src dst 47 0 1)
abbrev transfer (src dst : Fin 56) : Cmd 8 56 := .call (transferProgram src dst 0 1)
abbrev clear (src : Fin 56) : Cmd 8 56 := .call (clearProgram src 0 1)

abbrev scale : Cmd 8 56 := .call (ProgramLinking.liftProgram Squarefree.ScaleProgram.program id scalePorts)
abbrev keyMap : Cmd 8 56 := .call (ProgramLinking.liftProgram Squarefree.KeyMapProgram.scanProgram id keyPorts)
abbrev normalize : Cmd 8 56 := .call (ProgramLinking.liftProgram Normalize.program id normalizePorts)

abbrev read : Cmd 8 56 := .seq (Squarefree.Program.readFrame8 40 43)
  (.seq (Squarefree.Program.readFrame8 40 48) (transfer 48 44))

abbrev scalePhase : Cmd 8 56 := .seq (copy 41 32) (.seq (copy 44 34)
  (.seq scale (.seq (clear 34) (clear 44))))

abbrev keyPhase : Cmd 8 56 := .seq (copy 38 0) (.seq (clear 38)
  (.seq (transfer 43 1) (.seq (copy 45 2) (.seq (copy 46 3)
    (.seq keyMap (.seq (clear 1) (.seq (clear 2) (clear 3))))))))

abbrev normalizePhase : Cmd 8 56 := .seq (copy 4 27) (.seq (clear 4)
  (.seq (copy 39 51) (.seq normalize (clear 51))))

abbrev step : Cmd 8 56 := .seq read (.seq scalePhase (.seq keyPhase normalizePhase))
abbrev peek : Cmd 8 56 := .base (.atom (.peek 40 0 7))
abbrev loop : Cmd 8 56 := .while 7 (.seq step peek)
abbrev command : Cmd 8 56 := .seq peek loop
def program := compiled command 40 42

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

structure Store where
  modulus : List Bool := []
  width : List Bool := []
  zero : List Bool := []
  table : List Bool := []
  degree : List Bool := []
  left : List Bool := []
  right : List Bool := []
  acc : List Bool := []
  key : List Bool := []
  coeff : List Bool := []
  uCap : List Bool := []
  zCap : List Bool := []
  scaled : List Bool := []
  mapped : List Bool := []
  scaleSource : List Bool := []
  scalar : List Bool := []
  keySource : List Bool := []
  keyLeft : List Bool := []
  keyUCap : List Bool := []
  keyZCap : List Bool := []
  normalSource : List Bool := []
  normalCount : List Bool := []
  reversedCoeff : List Bool := []

def tapes (s : Store) : Fin 56 → List Bool := fun i =>
  if i=0 then s.keySource else if i=1 then s.keyLeft else
  if i=2 then s.keyUCap else if i=3 then s.keyZCap else
  if i=4 then s.mapped else if i=5 then s.modulus else
  if i=12 then s.width else if i=17 then s.zero else
  if i=22 then s.table else if i=27 then s.normalSource else
  if i=32 then s.scaleSource else if i=34 then s.scalar else
  if i=38 then s.scaled else if i=39 then s.degree else
  if i=40 then s.left else if i=41 then s.right else
  if i=42 then s.acc else if i=43 then s.key else
  if i=44 then s.coeff else if i=45 then s.uCap else
  if i=46 then s.zCap else if i=48 then s.reversedCoeff else
  if i=51 then s.normalCount else []

def state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs,tapes s⟩

/-- Common product idle store: caches and runtime controls only. -/
def idle (modulus width zero table degree uCap zCap : List Bool) : Store :=
  {modulus := modulus, width := width, zero := zero, table := table,
    degree := degree, uCap := uCap, zCap := zCap}

def input (modulus width zero table degree uCap zCap left right : List Bool) : Store :=
  {idle modulus width zero table degree uCap zCap with left := left, right := right}

def output (modulus width zero table degree uCap zCap right result : List Bool) : Store :=
  {idle modulus width zero table degree uCap zCap with right := right, acc := result}

def afterCopy (d : Data) (src dst : Fin 56) : Data :=
  ⟨readRegs d.regs 0 1 none,copyStacks src dst d.stacks⟩
def afterTransfer (d : Data) (src dst : Fin 56) : Data :=
  ⟨readRegs d.regs 0 1 none,transferStacks src dst d.stacks⟩
def afterClear (d : Data) (src : Fin 56) : Data :=
  ⟨readRegs d.regs 0 1 none,clearStacks src d.stacks⟩

theorem copy_eval (d : Data) (src dst : Fin 56)
    (hsd : src ≠ dst) (hst : src ≠ 47) (htd : (47 : Fin 56) ≠ dst) (htmp : d.stacks 47 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (afterCopy d src dst) := by
  exact .call _ (ListRegisterProgram.copy_run src dst 47 0 1 hsd hst htd (by decide) d.regs d.stacks htmp)

theorem transfer_eval (d : Data) (src dst : Fin 56) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (afterTransfer d src dst) := by
  exact Squarefree.Program.transfer8_eval d src dst hsd

theorem clear_eval (d : Data) (src : Fin 56) :
    Eval (clear src) (2*(d.stacks src).length+3) d (afterClear d src) := by
  apply Eval.call
  have h := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  simpa only [clearResult,afterClear,StructuredProgram.State.withPC,Nat.add_assoc] using hh

theorem copy_state (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 56)
    (hsd : src ≠ dst) (hst : src ≠ 47) (htd : (47 : Fin 56) ≠ dst)
    (hs : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterCopy,state,hs] using copy_eval (state regs a) src dst hsd hst htd rfl

theorem transfer_state (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 56)
    (hsd : src ≠ dst) (hs : transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterTransfer,state,hs] using transfer_eval (state regs a) src dst hsd

theorem clear_state (regs : Fin 8 → Bool) (a b : Store) (src : Fin 56)
    (hs : clearStacks src (tapes a) = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterClear,state,hs] using clear_eval (state regs a) src


theorem read_state (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 56)
    (hsd : src ≠ dst) (bits tail : List Bool)
    (hin : tapes a src = Encoding.frame bits ++ tail)
    (hs : Function.update (Function.update (tapes a) src tail) dst
      (bits.reverse ++ tapes a dst) = tapes b) :
    Eval (Squarefree.Program.readFrame8 src dst) (6*bits.length+4) (state regs a)
      (state (readRegs regs 0 1 (some false)) b) := by
  simpa only [state,Squarefree.Program.afterFrame8,hs] using
    Squarefree.Program.readFrame8_eval (state regs a) src dst hsd bits tail hin

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copyRight_eval (regs : Fin 8 → Bool) (a : Store) (he : a.scaleSource = []) :
    Eval (copy 41 32) (7*a.right.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with scaleSource := a.right }) := by
  apply copy_state regs a _ 41 32 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyCoefficient_eval (regs : Fin 8 → Bool) (a : Store) (he : a.scalar = []) :
    Eval (copy 44 34) (7*a.coeff.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with scalar := a.coeff }) := by
  apply copy_state regs a _ 44 34 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyScaled_eval (regs : Fin 8 → Bool) (a : Store) (he : a.keySource = []) :
    Eval (copy 38 0) (7*a.scaled.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with keySource := a.scaled }) := by
  apply copy_state regs a _ 38 0 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyUCap_eval (regs : Fin 8 → Bool) (a : Store) (he : a.keyUCap = []) :
    Eval (copy 45 2) (7*a.uCap.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with keyUCap := a.uCap }) := by
  apply copy_state regs a _ 45 2 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyZCap_eval (regs : Fin 8 → Bool) (a : Store) (he : a.keyZCap = []) :
    Eval (copy 46 3) (7*a.zCap.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with keyZCap := a.zCap }) := by
  apply copy_state regs a _ 46 3 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyMapped_eval (regs : Fin 8 → Bool) (a : Store) (he : a.normalSource = []) :
    Eval (copy 4 27) (7*a.mapped.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with normalSource := a.mapped }) := by
  apply copy_state regs a _ 4 27 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyDegree_eval (regs : Fin 8 → Bool) (a : Store) (he : a.normalCount = []) :
    Eval (copy 39 51) (7*a.degree.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with normalCount := a.degree }) := by
  apply copy_state regs a _ 39 51 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem transferKey_eval (regs : Fin 8 → Bool) (a : Store) (he : a.keyLeft = []) :
    Eval (transfer 43 1) (3*a.key.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with key := [], keyLeft := a.key.reverse }) := by
  apply transfer_state regs a _ 43 1 (by decide)
  funext i; fin_cases i <;> simp [transferStacks,tapes,he]

theorem transferCoefficient_eval (regs : Fin 8 → Bool) (a : Store) (he : a.coeff = []) :
    Eval (transfer 48 44) (3*a.reversedCoeff.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with reversedCoeff := [], coeff := a.reversedCoeff.reverse }) := by
  apply transfer_state regs a _ 48 44 (by decide)
  funext i; fin_cases i <;> simp [transferStacks,tapes,he]

theorem clearScalar_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 34) (2*a.scalar.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with scalar := [] }) := by
  apply clear_state regs a _ 34
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearCoefficient_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 44) (2*a.coeff.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with coeff := [] }) := by
  apply clear_state regs a _ 44
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearScaled_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 38) (2*a.scaled.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with scaled := [] }) := by
  apply clear_state regs a _ 38
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearKeyLeft_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 1) (2*a.keyLeft.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with keyLeft := [] }) := by
  apply clear_state regs a _ 1
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearKeyUCap_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 2) (2*a.keyUCap.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with keyUCap := [] }) := by
  apply clear_state regs a _ 2
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearKeyZCap_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 3) (2*a.keyZCap.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with keyZCap := [] }) := by
  apply clear_state regs a _ 3
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearMapped_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 4) (2*a.mapped.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with mapped := [] }) := by
  apply clear_state regs a _ 4
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearNormalCount_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 51) (2*a.normalCount.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with normalCount := [] }) := by
  apply clear_state regs a _ 51
  funext i; fin_cases i <;> simp [clearStacks,tapes]

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 def scaleEnvironment (a : Store) (scalar : List Bool) : Squarefree.ScaleProgram.Environment :=
  ⟨a.modulus,a.width,a.zero,a.table,scalar,a.degree⟩

theorem embed_scale (regs rr : Fin 8 → Bool) (a : Store) (source scalar output : List Bool)
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = []) :
    embedState id scalePorts (state regs a)
      (Squarefree.ScaleProgram.state rr { Squarefree.ScaleProgram.idle (scaleEnvironment a scalar) source [] with output := output }) =
    state rr { a with scaleSource := source, scalar := scalar, scaled := output } := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scalePorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> simp [scalePorts,state,tapes,scaleEnvironment,
      Squarefree.ScaleProgram.state,Squarefree.ScaleProgram.tapes,Squarefree.ScaleProgram.idle,
      Squarefree.ScaleProgram.nativeIdle,h0,h1,h2,h3,h4,h27]
  · intro i hi
    fin_cases i <;> first | rfl | (exfalso; apply hi; decide)

theorem embed_keyMap (regs rr : Fin 8 → Bool) (a : Store)
    (source left t J output : List Bool) :
    embedState id keyPorts (state regs a)
      (Squarefree.KeyMapProgram.state rr (Squarefree.KeyMapProgram.idle ⟨left,t,J⟩ source output)) =
    state rr { a with keySource := source, keyLeft := left, keyUCap := t, keyZCap := J, mapped := output } := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id keyPorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> first | rfl | (exfalso; apply hi; decide)

theorem embed_normalize (regs rr : Fin 8 → Bool) (a : Store) (dict source count : List Bool)
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) :
    embedState id normalizePorts (state regs a)
      (Normalize.state rr a.modulus a.width count dict source) =
    state rr { a with acc := dict, normalSource := source, normalCount := count } := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id normalizePorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> simp [normalizePorts,state,tapes,Normalize.state,Normalize.extend,
      Dictionary.machine,Dictionary.tapes,Dictionary.outputTape,h0,h1,h2,h3,h4,Fin.snoc]
    all_goals first | rfl
  · intro i hi
    fin_cases i <;> first | rfl | (exfalso; apply hi; decide)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

omit [DecidableEq K] in
theorem scale_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (he : scaleEnvironment a a.scalar = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
    (hs : a.scaleSource = Squarefree.ScaleProgram.encode key entries) (ho : a.scaled = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = []) :
    ∃ n ≤ Squarefree.ScaleProgram.budget key entries + 1, ∃ rr,
      Eval scale n (state regs a)
        (state rr { a with scaleSource := [], scaled := Squarefree.ScaleProgram.encode key (Squarefree.ScaleProgram.scaled p t M cache table scalar entries) }) := by
  obtain ⟨rr,n,hn,ht⟩ := Squarefree.ScaleProgram.program_runsIn p t M cache hz table scalar degree width hd hw key entries regs
  have hh := eval_call_lifted Squarefree.ScaleProgram.program id scalePorts (state regs a)
    Function.injective_id scalePorts_injective ht
  rw [←he,←hs] at hh
  have ha : embedState id scalePorts (state regs a)
      (Squarefree.ScaleProgram.state regs (Squarefree.ScaleProgram.idle (scaleEnvironment a a.scalar) a.scaleSource [])) = state regs a := by
    have h := embed_scale regs regs a a.scaleSource a.scalar [] h0 h1 h2 h3 h4 h27
    have hs' : { a with scaleSource := a.scaleSource, scalar := a.scalar, scaled := [] } = a := by cases a; simp_all
    rw [hs'] at h
    exact h
  rw [ha,embed_scale _ _ _ _ _ _ h0 h1 h2 h3 h4 h27] at hh
  exact ⟨n,hn,rr,hh⟩

theorem keyMap_eval {n : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (regs : Fin 8 → Bool) (a : Store)
    (hl : a.keyLeft = Squarefree.encodeIndex left)
    (hu : a.keyUCap = List.replicate u true) (hj : a.keyZCap = List.replicate J true)
    (hs : a.keySource = Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (ho : a.mapped = []) :
    ∃ k ≤ Squarefree.KeyMapProgram.budget left u J entries + 2, ∃ rr,
      Eval keyMap k (state regs a)
        (state rr { a with keySource := [], mapped := Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped left u J entries).reverse) }) := by
  obtain ⟨k,hk,rr,ht⟩ := Squarefree.KeyMapProgram.scan_trace left u J entries [] regs
  have hh := eval_call_lifted Squarefree.KeyMapProgram.scanProgram id keyPorts (state regs a)
    Function.injective_id keyPorts_injective ht
  simp only [Squarefree.KeyMapProgram.environment,List.append_nil] at hh
  rw [←hl,←hu,←hj,←hs,embed_keyMap,embed_keyMap] at hh
  have ha : { a with keySource := a.keySource, keyLeft := a.keyLeft, keyUCap := a.keyUCap, keyZCap := a.keyZCap, mapped := [] } = a := by
    cases a; simp_all
  rw [ha] at hh
  exact ⟨k,hk,rr,hh⟩

theorem normalize_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (hm : a.modulus = M.bits) (hw : a.width.length = baseWidth p t) (hd : a.normalCount.length = d)
    (hsource : a.normalSource = Normalize.bytes key source) (hseed : a.acc = Normalize.bytes key seed)
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) :
    ∃ n ≤ Normalize.work p t M cache key source seed + 2, ∃ rr,
      Eval normalize n (state regs a)
        (state rr { a with normalSource := [], acc := Normalize.bytes key (Normalize.run p t M cache source seed) }) := by
  obtain ⟨rr,n,hn,ht⟩ := Normalize.program_run p t M cache key hk source seed regs a.width a.normalCount hd hw
  have hh := eval_call_lifted Normalize.program id normalizePorts (state regs a)
    Function.injective_id normalizePorts_injective ht
  rw [←hm,←hsource,←hseed,embed_normalize _ _ _ _ _ _ h0 h1 h2 h3 h4,
    embed_normalize _ _ _ _ _ _ h0 h1 h2 h3 h4] at hh
  have ha : { a with acc := a.acc, normalSource := a.normalSource, normalCount := a.normalCount } = a := by cases a; rfl
  rw [ha] at hh
  exact ⟨n,hn,rr,hh⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem read_eval (regs : Fin 8 → Bool) (a : Store) (key coeff tail : List Bool)
    (hin : a.left = Encoding.frame key ++ Encoding.frame coeff ++ tail)
    (hk : a.key = []) (hc : a.coeff = []) (hr : a.reversedCoeff = []) :
    Eval read (6*key.length+9*coeff.length+11) (state regs a)
      (state (readRegs regs 0 1 none) {a with left := tail, key := key.reverse, coeff := coeff}) := by
  let b : Store := {a with left := Encoding.frame coeff ++ tail, key := key.reverse}
  let c : Store := {b with left := tail, reversedCoeff := coeff.reverse}
  have h1 := read_state regs a b 40 43 (by decide) key (Encoding.frame coeff ++ tail)
    (by simpa [tapes, List.append_assoc] using hin)
    (by funext i; fin_cases i <;> first | rfl | simp [tapes,b,hk])
  have h2 := read_state (readRegs regs 0 1 (some false)) b c 40 48 (by decide) coeff tail rfl
    (by funext i; fin_cases i <;> first | rfl | simp [tapes,c,b,hr])
  have h3 := transferCoefficient_eval (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false)) c hc
  have he := h1.seq (h2.seq h3)
  convert he using 1
  · simp only [c,List.length_reverse]
    omega
  · simp only [b,c,List.reverse_reverse,readRegs_reset]
    apply congrArg (state (readRegs regs 0 1 none))
    cases a
    simp_all

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

omit [DecidableEq K] in
theorem scalePhase_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (he : scaleEnvironment a a.coeff = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
    (hr : a.right = Squarefree.ScaleProgram.encode key entries)
    (hs : a.scaleSource = []) (hc : a.scalar = []) (ho : a.scaled = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = []) :
    ∃ n ≤ 7*a.right.length+11*a.coeff.length+Squarefree.ScaleProgram.budget key entries+17, ∃ rr,
      Eval scalePhase n (state regs a)
        (state rr {a with coeff := [], scaled := Squarefree.ScaleProgram.encode key (Squarefree.ScaleProgram.scaled p t M cache table scalar entries)}) := by
  let b : Store := {a with scaleSource := a.right}
  let c : Store := {b with scalar := b.coeff}
  let output := Squarefree.ScaleProgram.encode key (Squarefree.ScaleProgram.scaled p t M cache table scalar entries)
  let f : Store := {c with scaleSource := [], scaled := output}
  let g : Store := {f with scalar := []}
  have hcopyB := copyRight_eval regs a hs
  have hcopyC := copyCoefficient_eval (readRegs regs 0 1 none) b hc
  obtain ⟨n,hn,rr,hscale⟩ := scale_eval p t M cache hz table scalar degree width hd hw key entries
    (readRegs (readRegs regs 0 1 none) 0 1 none) c he hr ho h0 h1 h2 h3 h4 h27
  have hclearC := clearScalar_eval rr f
  have hclearInput := clearCoefficient_eval (readRegs rr 0 1 none) g
  have run := hcopyB.seq (hcopyC.seq (hscale.seq (hclearC.seq hclearInput)))
  refine ⟨_,?_,readRegs (readRegs rr 0 1 none) 0 1 none,(by
    convert run using 1
    apply congrArg (state (readRegs (readRegs rr 0 1 none) 0 1 none))
    cases a
    simp_all [b,c,f,g,output])⟩
  dsimp [b,c,f,g,output] at hn ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem keyPhase_eval {n : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (regs : Fin 8 → Bool) (a : Store)
    (hl : a.key = (Squarefree.encodeIndex left).reverse)
    (hu : a.uCap = List.replicate u true) (hj : a.zCap = List.replicate J true)
    (hs : a.scaled = Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) :
    ∃ k ≤ 9*a.scaled.length+5*a.key.length+9*a.uCap.length+9*a.zCap.length+
      Squarefree.KeyMapProgram.budget left u J entries+32, ∃ rr,
      Eval keyPhase k (state regs a)
        (state rr {a with scaled := [], key := [], mapped := Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped left u J entries).reverse)}) := by
  let b : Store := {a with keySource := a.scaled}
  let c : Store := {b with scaled := []}
  let d : Store := {c with key := [], keyLeft := c.key.reverse}
  let e : Store := {d with keyUCap := d.uCap}
  let f : Store := {e with keyZCap := e.zCap}
  let out := Squarefree.Program.rawEntries
    (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped left u J entries).reverse)
  let g : Store := {f with keySource := [], mapped := out}
  let h : Store := {g with keyLeft := []}
  let i : Store := {h with keyUCap := []}
  have hcopy := copyScaled_eval regs a h0
  have hclear := clearScaled_eval (readRegs regs 0 1 none) b
  have hkey := transferKey_eval (readRegs (readRegs regs 0 1 none) 0 1 none) c h1
  have huc := copyUCap_eval (readRegs (readRegs (readRegs regs 0 1 none) 0 1 none) 0 1 none) d h2
  have hjc := copyZCap_eval (readRegs (readRegs (readRegs (readRegs regs 0 1 none) 0 1 none) 0 1 none) 0 1 none) e h3
  obtain ⟨k,hk,rr,hmap⟩ := keyMap_eval left u J entries
    (readRegs (readRegs (readRegs (readRegs (readRegs regs 0 1 none) 0 1 none) 0 1 none) 0 1 none) 0 1 none) f
    (by simp [f,e,d,c,b,hl]) hu hj hs h4
  have hcl := clearKeyLeft_eval rr g
  have hcu := clearKeyUCap_eval (readRegs rr 0 1 none) h
  have hcj := clearKeyZCap_eval (readRegs (readRegs rr 0 1 none) 0 1 none) i
  have run := hcopy.seq (hclear.seq (hkey.seq (huc.seq (hjc.seq (hmap.seq (hcl.seq (hcu.seq hcj)))))))
  refine ⟨_,?_,readRegs (readRegs (readRegs rr 0 1 none) 0 1 none) 0 1 none,(by
    convert run using 1
    apply congrArg (state (readRegs (readRegs (readRegs rr 0 1 none) 0 1 none) 0 1 none))
    cases a
    simp_all [b,c,d,e,f,g,h,i,out])⟩
  dsimp [b,c,d,e,f,g,h,i,out] at hk ⊢
  simp only [List.length_reverse]
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

theorem normalizePhase_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (hm : a.modulus = M.bits) (hw : a.width.length = baseWidth p t) (hd : a.degree.length = d)
    (hsource : a.mapped = Normalize.bytes key source) (hseed : a.acc = Normalize.bytes key seed)
    (hs : a.normalSource = []) (hc : a.normalCount = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = []) (h3 : a.keyZCap = []) :
    ∃ n ≤ 9*a.mapped.length+9*a.degree.length+Normalize.work p t M cache key source seed+18,
    ∃ rr, Eval normalizePhase n (state regs a)
      (state rr {a with mapped := [], acc := Normalize.bytes key (Normalize.run p t M cache source seed)}) := by
  let b : Store := {a with normalSource := a.mapped}
  let c : Store := {b with mapped := []}
  let f : Store := {c with normalCount := c.degree}
  let g : Store := {f with normalSource := [], acc := Normalize.bytes key (Normalize.run p t M cache source seed)}
  have hcopy := copyMapped_eval regs a hs
  have hclear := clearMapped_eval (readRegs regs 0 1 none) b
  have hcount := copyDegree_eval (readRegs (readRegs regs 0 1 none) 0 1 none) c hc
  obtain ⟨n,hn,rr,hN⟩ := normalize_eval p t M cache key hk source seed
    (readRegs (readRegs (readRegs regs 0 1 none) 0 1 none) 0 1 none) f
    hm hw hd hsource hseed h0 h1 h2 h3 rfl
  have hclean := clearNormalCount_eval rr g
  have hrun := hcopy.seq (hclear.seq (hcount.seq (hN.seq hclean)))
  refine ⟨_,?_,readRegs rr 0 1 none,(by
    convert hrun using 1
    apply congrArg (state (readRegs rr 0 1 none))
    cases a
    simp_all [b,c,f,g])⟩
  dsimp [b,c,f,g] at hn ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Entry (n B d : ℕ) := Squarefree.Index (Fin n) × RingProgram.Code (Word B) d

def coefficientBytes {n B d : ℕ} (entries : List (Entry n B d)) : List (Squarefree.KeyMapProgram.Entry n) :=
  entries.map fun a => (a.1,RingProgram.flat a.2)

def keptJoin {n B d : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ) : List (Entry n B d) → List (Entry n B d)
  | [] => []
  | (b,c)::rest => if (left.join b).Kept u J then (left.join b,c)::keptJoin left u J rest
      else keptJoin left u J rest

theorem coefficientBytes_join {n B d : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) :
    Squarefree.KeyMapProgram.mapped left u J (coefficientBytes entries) =
      coefficientBytes (keptJoin left u J entries) := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
    rcases a with ⟨b,c⟩
    simp only [coefficientBytes] at ih
    by_cases h : (left.join b).Kept u J <;>
      simp [coefficientBytes,keptJoin,Squarefree.KeyMapProgram.mapped,h,ih]

theorem coefficientBytes_reverse {n B d : ℕ} (entries : List (Entry n B d)) :
    (coefficientBytes entries).reverse = coefficientBytes entries.reverse := by
  simp [coefficientBytes]

theorem encoded_coefficientBytes {n B d : ℕ} (entries : List (Entry n B d)) :
    Squarefree.KeyMapProgram.encoded (coefficientBytes entries) =
      Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries := by
  simp [coefficientBytes,Squarefree.KeyMapProgram.encoded,Squarefree.Program.encodeDictionary,
    List.map_map,Function.comp_def]

def block (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :=
  (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)).reverse

/-- Runtime persistent context. Every non-context low stack is initially empty. -/
def environment (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (u J : ℕ) : Store :=
  idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)

def working (e : Store) {n B d : ℕ} (left right acc : List (Entry n B d)) : Store :=
  {e with left := Normalize.bytes Squarefree.encodeIndex left, right := Normalize.bytes Squarefree.encodeIndex right, acc := Normalize.bytes Squarefree.encodeIndex acc}

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev bytes {n B d : ℕ} := @Normalize.bytes (Squarefree.Index (Fin n)) B d Squarefree.encodeIndex

def stepBudget (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right seed : List (Entry n (baseWidth p t) d)) : ℕ :=
  let scaled := Squarefree.ScaleProgram.scaled p t M cache table a.2 right
  let source := block p t M cache table u J a right
  (6*(Squarefree.encodeIndex a.1).length+9*(RingProgram.flat a.2).length+11) +
  (7*(bytes right).length+11*(RingProgram.flat a.2).length+
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex right+17) +
  (9*(bytes scaled).length+5*(Squarefree.encodeIndex a.1).length+9*u+9*J+
    Squarefree.KeyMapProgram.budget a.1 u J (coefficientBytes scaled)+32) +
  (9*(bytes source).length+9*d+Normalize.work p t M cache Squarefree.encodeIndex source seed+18)

theorem block_bytes (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded
      (Squarefree.KeyMapProgram.mapped a.1 u J
        (coefficientBytes (Squarefree.ScaleProgram.scaled p t M cache table a.2 right))).reverse) =
      bytes (block p t M cache table u J a right) := by
  rw [coefficientBytes_join,coefficientBytes_reverse,encoded_coefficientBytes]
  rfl

theorem step_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (a : Entry n (baseWidth p t) d)
    (left right seed : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ k ≤ stepBudget p t M cache table u J a right seed, ∃ rr,
      Eval step k (state regs (working (environment p t M cache table degree width u J) (a::left) right seed))
        (state rr (working (environment p t M cache table degree width u J) left right
          (Normalize.run p t M cache (block p t M cache table u J a right) seed))) := by
  let e := environment p t M cache table degree width u J
  let start := working e (a::left) right seed
  let b : Store := {start with left := bytes left, key := (Squarefree.encodeIndex a.1).reverse, coeff := RingProgram.flat a.2}
  let scaled := Squarefree.ScaleProgram.scaled p t M cache table a.2 right
  let c : Store := {b with coeff := [], scaled := bytes scaled}
  let source := block p t M cache table u J a right
  let f : Store := {c with scaled := [], key := [], mapped := bytes source}
  have hr := read_eval regs start (Squarefree.encodeIndex a.1) (RingProgram.flat a.2) (bytes left) rfl rfl rfl rfl
  obtain ⟨k1,hk1,r1,hs⟩ := scalePhase_eval p t M cache hz table a.2 degree width hd hw
    Squarefree.encodeIndex right (readRegs regs 0 1 none) b rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨k2,hk2,r2,hk⟩ := keyPhase_eval a.1 u J (coefficientBytes scaled) r1 c rfl rfl rfl
    (by rw [encoded_coefficientBytes]; rfl) rfl rfl rfl rfl rfl
  rw [block_bytes p t M cache table u J a right] at hk
  obtain ⟨k3,hk3,r3,hn⟩ := normalizePhase_eval p t M cache Squarefree.encodeIndex
    Squarefree.encodeIndex_injective source seed r2 f rfl hw hd rfl rfl rfl rfl rfl rfl rfl rfl
  have hrun := hr.seq (hs.seq (hk.seq hn))
  refine ⟨6*(Squarefree.encodeIndex a.1).length+9*(RingProgram.flat a.2).length+11+(k1+(k2+k3)),?_,r3,?_⟩
  · dsimp [b,c,f,start,e,working,environment,idle,scaled,source] at hk1 hk2 hk3
    simp only [List.length_reverse,List.length_replicate] at hk2
    rw [hd] at hk3
    dsimp [stepBudget]
    simp only [bytes] at hk1 hk2 hk3 ⊢
    omega
  · exact hrun

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ) :
    List (Entry n (baseWidth p t) d) → List (Entry n (baseWidth p t) d) →
      List (Entry n (baseWidth p t) d) → List (Entry n (baseWidth p t) d)
  | [], _, seed => seed
  | a::left, right, seed => run p t M cache table u J left right
      (Normalize.run p t M cache (block p t M cache table u J a right) seed)

def work (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ) :
    List (Entry n (baseWidth p t) d) → List (Entry n (baseWidth p t) d) →
      List (Entry n (baseWidth p t) d) → ℕ
  | [], _, _ => 1
  | a::left, right, seed => stepBudget p t M cache table u J a right seed + 2 +
      work p t M cache table u J left right
        (Normalize.run p t M cache (block p t M cache table u J a right) seed)

def ready (regs : Fin 8 → Bool) (a : Store) : Data :=
  state (readRegs regs 0 7 a.left.head?) a

theorem peek_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval peek 1 (state regs a) (ready regs a) := .base (.atom _ _)

theorem ready_nil {n B d : ℕ} (regs : Fin 8 → Bool) (e : Store)
    (right seed : List (Entry n B d)) : (ready regs (working e [] right seed)).regs 7 = false := by
  simp [ready,state,working,readRegs,Normalize.bytes,Squarefree.Program.rawEntries,
    Squarefree.Program.encodeDictionary]

theorem ready_cons {n B d : ℕ} (regs : Fin 8 → Bool) (e : Store)
    (a : Entry n B d) (left right seed : List (Entry n B d)) :
    (ready regs (working e (a::left) right seed)).regs 7 = true := by
  cases hk : Squarefree.encodeIndex a.1 <;>
    simp [ready,state,working,readRegs,Normalize.bytes,Squarefree.Program.rawEntries,
      Squarefree.Program.encodeDictionary,Encoding.frame,hk]

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right seed : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ k ≤ work p t M cache table u J left right seed, ∃ rr,
      Eval loop k (ready regs (working (environment p t M cache table degree width u J) left right seed))
        (state rr (working (environment p t M cache table degree width u J) [] right
          (run p t M cache table u J left right seed))) := by
  induction left generalizing seed regs with
  | nil =>
    exact ⟨1,le_rfl,readRegs regs 0 7 none,Eval.while_false (ready_nil regs _ right seed)⟩
  | cons a left ih =>
    let initial := readRegs regs 0 7 (bytes (a::left)).head?
    let next := Normalize.run p t M cache (block p t M cache table u J a right) seed
    obtain ⟨k,hk,r1,hs⟩ := step_eval p t M cache hz table degree width hd hw u J a left right seed initial
    obtain ⟨v,hv,rr,ht⟩ := ih next r1
    have hp := peek_eval r1 (working (environment p t M cache table degree width u J) left right next)
    have hrun := Eval.while_true (ready_cons regs _ a left right seed) (hs.seq hp) ht
    exact ⟨_,by dsimp only [next] at hv; dsimp [work]; omega,rr,hrun⟩

theorem program_run_seed (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right seed : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ rr, RunsIn program (work p t M cache table u J left right seed+2)
      ((state regs (working (environment p t M cache table degree width u J) left right seed)).withPC
        (some program.entry))
      ((state rr (working (environment p t M cache table degree width u J) [] right
        (run p t M cache table u J left right seed))).withPC none) := by
  obtain ⟨k,hk,rr,he⟩ := loop_eval p t M cache hz table degree width hd hw u J left right seed regs
  have hrun := (peek_eval regs _).seq he
  exact ⟨rr,1+k+1,by omega,compiled_halt_trace hrun 40 42⟩

/-- Public product ABI, with all scratch stacks empty at return. -/
theorem program_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ rr, RunsIn program (work p t M cache table u J left right []+2)
      ((state regs (input M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
        (List.replicate u true) (List.replicate J true) (bytes left) (bytes right))).withPC (some program.entry))
      ((state rr (output M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
        (List.replicate u true) (List.replicate J true) (bytes right)
        (bytes (run p t M cache table u J left right [])))).withPC none) := by
  simpa only [working,environment,input,output,idle,Normalize.bytes,Squarefree.Program.encodeDictionary,List.map_nil,Squarefree.Program.rawEntries] using
    program_run_seed p t M cache hz table degree width hd hw u J left right [] regs

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
