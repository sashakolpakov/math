import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramRead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramLookup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanService
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseRing
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramAlgebra

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 40

structure Store where
  native : RingScan.ServiceStore
  source : List Bool := []
  accum : List Bool := []
  scalar : List Bool := []
  key : List Bool := []
  coeff : List Bool := []
  frame : List Bool := []
  output : List Bool := []
  count : List Bool := []

def tapes (s : Store) (i : Fin 40) : List Bool :=
  if i = 0 then s.native.result else if i = 5 then s.native.modulus
  else if i = 8 then s.native.x else if i = 9 then s.native.y
  else if i = 11 then s.native.degree else if i = 12 then s.native.width
  else if i = 15 then s.native.outer else if i = 16 then s.native.inner
  else if i = 17 then s.native.zero else if i = 20 then s.native.tableWork
  else if i = 21 then s.native.reverseStream else if i = 22 then s.native.table
  else if i = 23 then s.native.stream else if i = 32 then s.source
  else if i = 33 then s.accum else if i = 34 then s.scalar
  else if i = 35 then s.key else if i = 36 then s.coeff
  else if i = 37 then s.frame else if i = 38 then s.output
  else if i = 39 then s.count else []

def state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

def nativePorts : Fin 32 → Fin 40 := Fin.castAdd 8

theorem nativePorts_injective : Function.Injective nativePorts :=
  Fin.castAdd_injective _ _

theorem embed_native (regs rr : Fin 8 → Bool) (s : Store) (native : RingScan.ServiceStore) :
    embedState id nativePorts (state regs s) (RingScan.serviceWorkState rr native) =
      state rr {s with native := native} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id nativePorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;>
      simp [state, tapes, nativePorts, RingScan.serviceWorkState, RingScan.serviceTapes]
  · intro i hi
    apply Fin.addCases (m := 32) (n := 8) (motive := fun i =>
      i ∉ Set.range nativePorts → (state rr {s with native := native}).stacks i =
        (state regs s).stacks i) ?_ ?_ i hi
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j _; fin_cases j <;> simp [state, tapes]

abbrev copy (src dst : Fin 40) : Cmd 8 40 :=
  .call (copyProgram src dst 31 (0 : Fin 8) 1)

def copied (d : Data) (src dst : Fin 40) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩

theorem copy_eval (d : Data) (src dst : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ 31) (htd : (31 : Fin 40) ≠ dst)
    (htmp : d.stacks 31 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  exact .call _ (ListRegisterProgram.copy_run src dst 31 0 1
    hsd hst htd (by decide) d.regs d.stacks htmp)

abbrev peek : Cmd 8 40 := .base (.atom (.peek 32 0 7))

def peeked (d : Data) : Data := ⟨readRegs d.regs 0 7 (d.stacks 32).head?, d.stacks⟩

theorem peek_eval (d : Data) : Eval peek 1 d (peeked d) :=
  .base (.atom _ _)

def frameRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def framePorts (src : Fin 40) : Fin 2 → Fin 40 := ![src, 37]

theorem frameRegs_injective : Function.Injective frameRegs := Fin.castAdd_injective _ _

theorem framePorts_injective (src : Fin 40) (h : src ≠ 37) :
    Function.Injective (framePorts src) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [framePorts]

abbrev emitFrame (src : Fin 40) : Cmd 8 40 :=
  .call (ProgramLinking.liftProgram Program.frameEmitProgram frameRegs (framePorts src))

theorem emitFrame_eval (d : Data) (src : Fin 40) (h : src ≠ 37)
    (bits : List Bool) (hs : d.stacks src = bits.reverse) :
    ∃ rr, Eval (emitFrame src) (4 * bits.length + 6) d
      ⟨rr, Function.update (Function.update d.stacks src []) 37
        (Encoding.frame bits ++ d.stacks 37)⟩ := by
  obtain ⟨rf, ht⟩ := Program.frameEmit_trace bits (d.stacks 37) (d.regs ∘ frameRegs)
  let b := Program.frameData rf [] (Encoding.frame bits ++ d.stacks 37)
  let final := embedState frameRegs (framePorts src) d b
  have ha : embedState frameRegs (framePorts src) d
      (Program.frameData (d.regs ∘ frameRegs) bits.reverse (d.stacks 37)) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective (framePorts_injective src h)
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [framePorts, Program.frameData, hs]
    · intros; rfl
  have hb : final =
      (⟨final.regs, Function.update (Function.update d.stacks src []) 37
        (Encoding.frame bits ++ d.stacks 37)⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi37 : i = 37
      · subst i
        have hh := embedState_stack frameRegs (framePorts src) d b (framePorts_injective src h) 1
        simp only [Function.update_self]
        calc
          final.stacks 37 = b.stacks 1 := by
            rw [← show framePorts src (1 : Fin 2) = 37 by rfl]
            exact hh
          _ = Encoding.frame bits ++ d.stacks 37 := by rfl
      · by_cases his : i = src
        · subst i
          have hh := embedState_stack frameRegs (framePorts src) d b (framePorts_injective src h) 0
          simp only [Function.update_of_ne h, Function.update_self]
          calc
            final.stacks src = b.stacks 0 := by
              rw [← show framePorts src (0 : Fin 2) = src by rfl]
              exact hh
            _ = [] := by rfl
        · have hh := embedState_stack_frame frameRegs (framePorts src) d b i (by
            rintro ⟨j, hj⟩; fin_cases j <;> simp_all [framePorts])
          simp only [Function.update_of_ne hi37, Function.update_of_ne his]
          exact hh
  have he := eval_call_lifted Program.frameEmitProgram frameRegs (framePorts src) d
    frameRegs_injective (framePorts_injective src h) ht
  rw [ha] at he
  change Eval (emitFrame src) _ d final at he
  rw [hb] at he
  exact ⟨final.regs, he⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

structure Environment where
  modulus : List Bool
  width : List Bool
  zero : List Bool
  table : List Bool
  scalar : List Bool
  count : List Bool

def nativeIdle (e : Environment) : RingScan.ServiceStore :=
  { modulus := e.modulus, result := [], x := [], y := [], degree := [],
    width := e.width, zero := e.zero, table := e.table }

def idle (e : Environment) (source accum : List Bool) : Store :=
  ⟨nativeIdle e, source, accum, e.scalar, [], [], [], [], e.count⟩

theorem read_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (bits tail : List Bool)
    (hin : tapes a src = Encoding.frame bits ++ tail)
    (hout : Function.update (Function.update (tapes a) src tail) dst
      (bits.reverse ++ tapes a dst) = tapes b) :
    Eval (Program.readFrame8 src dst) (6*bits.length+4) (state regs a)
      (state (readRegs regs 0 1 (some false)) b) := by
  simpa only [state, Program.afterFrame8, hout] using
    Program.readFrame8_eval (state regs a) src dst hsd bits tail hin

theorem transfer_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (hout : transferStacks src dst (tapes a) = tapes b) :
    Eval (Program.transfer8 src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [state, Program.afterTransfer8, hout] using
    Program.transfer8_eval (state regs a) src dst hsd

theorem copy_store (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ 31) (htd : (31 : Fin 40) ≠ dst)
    (hout : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have hz : (state regs a).stacks 31 = [] := rfl
  simpa only [state, copied, hout] using
    copy_eval (state regs a) src dst hsd hst htd hz

theorem frame_store (regs : Fin 8 → Bool) (a b : Store) (src : Fin 40)
    (hne : src ≠ 37) (bits : List Bool) (hin : tapes a src = bits.reverse)
    (hout : Function.update (Function.update (tapes a) src []) 37
      (Encoding.frame bits ++ tapes a 37) = tapes b) :
    ∃ rr, Eval (emitFrame src) (4*bits.length+6) (state regs a) (state rr b) := by
  obtain ⟨rr, he⟩ := emitFrame_eval (state regs a) src hne bits hin
  exact ⟨rr, by simpa only [state, hout] using he⟩

abbrev prepare : Cmd 8 40 :=
  .seq (Program.readFrame8 32 35)
    (.seq (Program.readFrame8 32 36)
      (.seq (Program.transfer8 36 9) (.seq (copy 34 8) (copy 39 11))))

def prepared (e : Environment) (key coeff tail accum : List Bool) : Store :=
  {idle e tail accum with
    key := key.reverse
    native := {nativeIdle e with x := e.scalar, y := coeff, degree := e.count}}

theorem prepare_eval (regs : Fin 8 → Bool) (e : Environment)
    (key coeff tail accum : List Bool) :
    ∃ rr, Eval prepare
      (6*key.length+9*coeff.length+7*e.scalar.length+7*e.count.length+21)
      (state regs (idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) accum))
      (state rr (prepared e key coeff tail accum)) := by
  let a := idle e (Encoding.frame key ++ Encoding.frame coeff ++ tail) accum
  let b := {a with source := Encoding.frame coeff ++ tail, key := key.reverse}
  let c := {b with source := tail, coeff := coeff.reverse}
  let d := {c with coeff := [], native := {nativeIdle e with y := coeff}}
  let f := {d with native := {nativeIdle e with x := e.scalar, y := coeff}}
  let g := prepared e key coeff tail accum
  have h1 := read_store regs a b 32 35 (by decide) key (Encoding.frame coeff ++ tail)
    (by simp [a, idle, tapes, List.append_assoc])
    (by funext i; fin_cases i <;> simp [a,b,idle,tapes])
  have h2 := read_store (readRegs regs 0 1 (some false)) b c 32 36 (by decide) coeff tail
    (by rfl)
    (by funext i; fin_cases i <;> simp [b,c,a,idle,tapes])
  have h3 := transfer_store (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false))
    c d 36 9 (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,idle,nativeIdle,tapes,transferStacks])
  let r3 := readRegs (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false)) 0 1 none
  have h4 := copy_store r3 d f 34 8 (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,f,idle,nativeIdle,tapes,copyStacks])
  have h5 := copy_store (readRegs r3 0 1 none) f g 39 11 (by decide) (by decide) (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,c,d,f,g,prepared,idle,nativeIdle,tapes,copyStacks])
  refine ⟨readRegs (readRegs r3 0 1 none) 0 1 none, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 ;
    simp [a,b,c,d,f,idle,tapes] ; omega

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Emit stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def productReady (e : Environment) (key result tail accum : List Bool) : Store :=
  {idle e tail accum with
    key := key.reverse
    native := {nativeIdle e with result := result}}

/-- Emit one result into a reversed stream. Reversing the complete stream once
at the end restores the original record order. -/
abbrev emit : Cmd 8 40 :=
  .seq (Program.transfer8 0 36) (.seq (emitFrame 35)
    (.seq (Program.transfer8 37 33) (.seq (emitFrame 36) (Program.transfer8 37 33))))

theorem emit_eval (regs : Fin 8 → Bool) (e : Environment)
    (key result tail accum : List Bool) :
    ∃ rr, Eval emit (10*key.length+13*result.length+27)
      (state regs (productReady e key result tail accum))
      (state rr (idle e tail ((Encoding.frame key ++ Encoding.frame result).reverse ++ accum))) := by
  let a := productReady e key result tail accum
  let b := {idle e tail accum with key := key.reverse, coeff := result.reverse}
  let c := {idle e tail accum with coeff := result.reverse, frame := Encoding.frame key}
  let d := {idle e tail ((Encoding.frame key).reverse ++ accum) with coeff := result.reverse}
  let f := {idle e tail ((Encoding.frame key).reverse ++ accum) with frame := Encoding.frame result}
  let g := idle e tail ((Encoding.frame key ++ Encoding.frame result).reverse ++ accum)
  have h1 := transfer_store regs a b 0 36 (by decide)
    (by funext i; fin_cases i <;>
      simp [a,b,productReady,idle,nativeIdle,tapes,transferStacks])
  obtain ⟨r1,h2⟩ := frame_store (readRegs regs 0 1 none) b c 35 (by decide) key rfl
    (by funext i; fin_cases i <;>
      simp [b,c,idle,nativeIdle,tapes])
  have h3 := transfer_store r1 c d 37 33 (by decide)
    (by funext i; fin_cases i <;>
      simp [c,d,idle,nativeIdle,tapes,transferStacks])
  obtain ⟨r2,h4⟩ := frame_store (readRegs r1 0 1 none) d f 36 (by decide) result rfl
    (by funext i; fin_cases i <;>
      simp [d,f,idle,nativeIdle,tapes])
  have h5 := transfer_store r2 f g 37 33 (by decide)
    (by funext i; fin_cases i <;>
      simp [f,g,idle,nativeIdle,tapes,transferStacks,
        List.reverse_append,List.append_assoc])
  refine ⟨readRegs r2 0 1 none, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 ;
    simp [a,c,f,productReady,idle,nativeIdle,tapes] ; omega

abbrev finish : Cmd 8 40 := Program.transfer8 33 38

theorem finish_eval (regs : Fin 8 → Bool) (e : Environment) (output : List Bool) :
    Eval finish (3*output.length+3)
      (state regs (idle e [] output.reverse))
      (state (readRegs regs 0 1 none) {idle e [] [] with output := output}) := by
  have he := transfer_store regs (idle e [] output.reverse)
    {idle e [] [] with output := output} 33 38 (by decide)
    (by funext i; fin_cases i <;>
      simp [idle,nativeIdle,tapes,transferStacks])
  simpa [finish,idle,tapes,Fin.addCases] using he

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Native stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev multiply : Cmd 8 40 :=
  .call (ProgramLinking.liftProgram RingScan.serviceMulProgram id nativePorts)

def environment (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (degree width : List Bool) : Environment :=
  ⟨M.bits, width, cache.zero.val, RingTriple.tableEncoding table, RingProgram.flat scalar, degree⟩

def valueMul (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d) :=
  (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table scalar x).1

theorem multiply_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (key tail accum : List Bool) :
    ∃ n ≤ RingScan.serviceMulBudget (baseWidth p t) d + 1, ∃ rr,
      Eval multiply n
        (state regs (prepared (environment p t M cache table scalar degree width)
          key (RingProgram.flat x) tail accum))
        (state rr (productReady (environment p t M cache table scalar degree width)
          key (RingProgram.flat (valueMul p t M cache table scalar x)) tail accum)) := by
  obtain ⟨n,hn,rr,he⟩ := RingScan.serviceMul_eval p t M cache hz table scalar x regs degree width hd hw
  let start := prepared (environment p t M cache table scalar degree width)
    key (RingProgram.flat x) tail accum
  have hh := eval_call_lifted RingScan.serviceMulProgram id nativePorts (state regs start)
    Function.injective_id nativePorts_injective (compiled_halt_trace he 8 0)
  refine ⟨n+1, Nat.add_le_add_right hn 1, rr, ?_⟩
  simpa only [multiply, RingScan.serviceState, embed_native, start, prepared,
    productReady, environment, idle, nativeIdle, valueMul] using hh

abbrev step : Cmd 8 40 := .seq prepare (.seq multiply emit)

def stepBudget (B d keyLength : ℕ) : ℕ :=
  RingScan.serviceMulBudget B d + 16*keyLength + 29*(d*B) + 7*d + 49

theorem step_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar x : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (regs : Fin 8 → Bool) (key tail accum : List Bool) :
    ∃ n ≤ stepBudget (baseWidth p t) d key.length, ∃ rr,
      Eval step n
        (state regs (idle (environment p t M cache table scalar degree width)
          (Encoding.frame key ++ Encoding.frame (RingProgram.flat x) ++ tail) accum))
        (state rr (idle (environment p t M cache table scalar degree width) tail
          ((Encoding.frame key ++ Encoding.frame
            (RingProgram.flat (valueMul p t M cache table scalar x))).reverse ++ accum))) := by
  let e := environment p t M cache table scalar degree width
  obtain ⟨r1,h1⟩ := prepare_eval regs e key (RingProgram.flat x) tail accum
  obtain ⟨n,hn,r2,h2⟩ := multiply_eval p t M cache hz table scalar x degree width hd hw r1 key tail accum
  obtain ⟨r3,h3⟩ := emit_eval r2 e key
    (RingProgram.flat (valueMul p t M cache table scalar x)) tail accum
  refine ⟨_, ?_, r3, h1.seq (h2.seq h3)⟩
  simp only [RingProgram.flat_length]
  dsimp only [e,environment]
  simp only [RingProgram.flat_length]
  rw [hd]
  unfold stepBudget
  omega

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Loop stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

def encode {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) : List Bool :=
  Program.rawEntries (Program.encodeDictionary key RingProgram.flat entries)

@[simp] theorem encode_nil {B d : ℕ} (key : K → List Bool) :
    encode (B := B) (d := d) key [] = [] := rfl

@[simp] theorem encode_cons {B d : ℕ} (key : K → List Bool)
    (a : K × RingProgram.Code (Word B) d) (entries) :
    encode key (a :: entries) = Encoding.frame (key a.1) ++
      Encoding.frame (RingProgram.flat a.2) ++ encode key entries := rfl

def scaled (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :=
  entries.map (fun a => (a.1, valueMul p t M cache table scalar a.2))

theorem scaled_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (entries) :
    (scaled (K := K) p t M cache table scalar entries).map Prod.fst = entries.map Prod.fst := by
  simp [scaled, List.map_map, Function.comp_def]

abbrev loop : Cmd 8 40 := .while 7 (.seq step peek)

def loopBudget {B d : ℕ} (key : K → List Bool) :
    List (K × RingProgram.Code (Word B) d) → ℕ
  | [] => 1
  | a :: entries => stepBudget B d (key a.1).length + 2 + loopBudget key entries

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) (accum : List Bool) :
    ∃ n ≤ loopBudget key entries, ∃ rr,
      Eval loop n
        (peeked (state regs (idle (environment p t M cache table scalar degree width)
          (encode key entries) accum)))
        (state rr (idle (environment p t M cache table scalar degree width) []
          ((encode key (scaled p t M cache table scalar entries)).reverse ++ accum))) := by
  induction entries generalizing regs accum with
  | nil =>
      refine ⟨1, le_rfl, readRegs regs 0 7 none, ?_⟩
      have hh : (peeked (state regs (idle (environment p t M cache table scalar degree width)
          (encode (B := baseWidth p t) (d := d) key []) accum))).regs 7 = false := by
        simp [peeked,state,idle,tapes,readRegs]
      simpa [scaled,encode,Program.encodeDictionary,Program.rawEntries,
        peeked,state,idle,tapes,Fin.addCases] using (Eval.while_false (body := .seq step peek) hh)
  | cons a entries ih =>
      let e := environment p t M cache table scalar degree width
      let input := encode key (a :: entries)
      let recordBits := Encoding.frame (key a.1) ++
        Encoding.frame (RingProgram.flat (valueMul p t M cache table scalar a.2))
      let r0 := readRegs regs 0 7 input.head?
      obtain ⟨n,hn,r1,h1⟩ := step_eval p t M cache hz table scalar a.2 degree width hd hw r0
        (key a.1) (encode key entries) accum
      have hpeek := peek_eval (state r1 (idle e (encode key entries) (recordBits.reverse ++ accum)))
      obtain ⟨m,hm,r2,h2⟩ := ih r1 (recordBits.reverse ++ accum)
      have hflag : (peeked (state regs (idle e input accum))).regs 7 = true := by
        cases hk : key a.1 <;>
          simp [peeked,state,idle,tapes,input,encode_cons,Encoding.frame,hk,readRegs]
      have hstep : Eval step n (peeked (state regs (idle e input accum)))
          (state r1 (idle e (encode key entries) (recordBits.reverse ++ accum))) := by
        simpa [e, recordBits, peeked, state, idle, tapes, Fin.addCases, input, encode_cons, r0] using h1
      have hh := Eval.while_true hflag (hstep.seq hpeek) h2
      refine ⟨n+1+m+1, ?_, r2, ?_⟩
      · simp only [loopBudget]
        omega
      · simpa only [loop, scaled, List.map_cons, encode_cons, List.reverse_append,
          List.append_assoc, e, recordBits, input] using hh

theorem encode_scaled_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (key : K → List Bool) (entries) :
    (encode key (scaled p t M cache table scalar entries)).length = (encode key entries).length := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
      simp only [scaled,List.map_cons,encode_cons,List.length_append,Encoding.length_frame,
        RingProgram.flat_length]
      simpa only [scaled] using congrArg (fun n => (2*(key a.1).length+1)+(2*(d*baseWidth p t)+1)+n) ih

abbrev command : Cmd 8 40 := .seq peek (.seq loop finish)
def program := compiled command 32 38

def budget {B d : ℕ} (key : K → List Bool) (entries : List (K × RingProgram.Code (Word B) d)) : ℕ :=
  loopBudget key entries + 3*(encode key entries).length + 4

theorem command_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget key entries, ∃ rr,
      Eval command n
        (state regs (idle (environment p t M cache table scalar degree width) (encode key entries) []))
        (state rr {idle (environment p t M cache table scalar degree width) [] [] with
          output := encode key (scaled p t M cache table scalar entries)}) := by
  let e := environment p t M cache table scalar degree width
  have h1 := peek_eval (state regs (idle e (encode key entries) []))
  obtain ⟨n,hn,r1,h2⟩ := loop_eval p t M cache hz table scalar degree width hd hw key entries regs []
  simp only [List.append_nil] at h2
  have h3 := finish_eval r1 e (encode key (scaled p t M cache table scalar entries))
  refine ⟨_, ?_, _, h1.seq (h2.seq h3)⟩
  rw [encode_scaled_length]
  dsimp only [budget]
  omega

theorem program_runsIn (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool) :
    ∃ rr, RunsIn program (budget key entries + 1)
      ((state regs (idle (environment p t M cache table scalar degree width) (encode key entries) [])).withPC
        (some program.entry))
      ((state rr {idle (environment p t M cache table scalar degree width) [] [] with
        output := encode key (scaled p t M cache table scalar entries)}).withPC none) := by
  obtain ⟨n,hn,rr,he⟩ := command_eval p t M cache hz table scalar degree width hd hw key entries regs
  exact ⟨rr,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 32 38⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

def keyBits {C : Type*} (key : K → List Bool) : List (K × C) → ℕ
  | [] => 0
  | a :: entries => (key a.1).length + keyBits key entries

theorem encode_length {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    (encode key entries).length = 2*keyBits key entries + entries.length*(2*(d*B)+2) := by
  induction entries with
  | nil => simp [encode,keyBits,Program.rawEntries,Program.encodeDictionary]
  | cons a entries ih =>
      simp only [encode_cons,List.length_append,Encoding.length_frame,RingProgram.flat_length,
        ih,keyBits,List.length_cons]
      ring

theorem loopBudget_eq {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    loopBudget key entries = entries.length*(RingScan.serviceMulBudget B d+29*(d*B)+7*d+51) +
      16*keyBits key entries+1 := by
  induction entries with
  | nil => simp [loopBudget,keyBits]
  | cons a entries ih => simp only [loopBudget,stepBudget,ih,keyBits,List.length_cons]; ring

theorem budget_eq {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d)) :
    budget key entries + 1 =
      entries.length*(RingScan.serviceMulBudget B d+35*(d*B)+7*d+57) +
      22*keyBits key entries+6 := by
  rw [budget,loopBudget_eq,encode_length]
  ring

theorem keyBits_le {C : Type*} (key : K → List Bool) (entries : List (K × C))
    (L : ℕ) (h : ∀ a ∈ entries, (key a.1).length ≤ L) :
    keyBits key entries ≤ entries.length*L := by
  induction entries with
  | nil => simp [keyBits]
  | cons a entries ih =>
      have ha := h a (by simp)
      have ht := ih (fun a ha => h a (by simp [ha]))
      simp only [keyBits,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem budget_le {B d : ℕ} (key : K → List Bool)
    (entries : List (K × RingProgram.Code (Word B) d))
    (L : ℕ) (h : ∀ a ∈ entries, (key a.1).length ≤ L) :
    budget key entries + 1 ≤
      entries.length*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*L+57)+6 := by
  rw [budget_eq]
  have hk := keyBits_le key entries L h
  have hs := RingScan.serviceMulBudget_le B d
  calc
    _ ≤ entries.length*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+57) +
        22*(entries.length*L)+6 :=
      Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left 22 hk)) 6
    _ = _ := by ring

theorem primitive_scale (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (entries) (regs : Fin 8 → Bool)
    (L : ℕ) (hL : ∀ a ∈ entries, (key a.1).length ≤ L) :
    ∃ rr, Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (entries.length*(40000*(d+1)^3*(baseWidth p t+1)^2+
          35*(d*baseWidth p t)+7*d+22*L+57)+6))
      (primitiveCfg program
        ((state regs (idle (environment p t M cache table scalar degree width) (encode key entries) [])).withPC
          (some program.entry)))
      (primitiveCfg program
        ((state rr {idle (environment p t M cache table scalar degree width) [] [] with
          output := encode key (scaled p t M cache table scalar entries)}).withPC none)) := by
  obtain ⟨rr,hr⟩ := program_runsIn p t M cache hz table scalar degree width hd hw key entries regs
  exact ⟨rr,(BitProgram.primitive_execution _ hr).mono
    (Nat.mul_le_mul_left _ (budget_le key entries L hL))⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Semantics stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {K V R : Type*} [DecidableEq V] [CommRing R]

def decoded (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) : List (K × R) :=
  entries.map (fun a => (a.1, RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis a.2))

theorem scaled_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (constant : RingProgram.Code (Word (baseWidth p t)) d) (entries)
    (h : (entries.map Prod.fst).Nodup) :
    ((scaled (K := K) p t M cache table constant entries).map Prod.fst).Nodup := by
  rwa [scaled_keys]

omit [DecidableEq V] in
theorem decoded_scaled (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (constant : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    decoded p t M cache scalar basis (scaled p t M cache table constant entries) =
      Sparse.scale (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis constant)
        (decoded p t M cache scalar basis entries) := by
  simp only [decoded,scaled,Sparse.scale,List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply]
  congr 1
  simpa only [valueMul,RingProgram.scalarRing_program] using
    RingProgram.denote_mul (RingProgram.scalarRing p t M cache) scalar basis table htable constant a.2

omit [DecidableEq V] in
theorem decoded_neg (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    decoded p t M cache scalar basis (scaled p t M cache table minusOne entries) =
      Sparse.neg (decoded p t M cache scalar basis entries) := by
  rw [decoded_scaled p t M cache scalar basis table htable,hminus]
  simp [Sparse.scale,Sparse.neg]

theorem denote_scaled (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (constant : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    Sparse.denote (decoded p t M cache scalar basis (scaled p t M cache table constant entries)) =
      Sparse.atom Index.origin
        (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis constant) *
          Sparse.denote (decoded p t M cache scalar basis entries) := by
  rw [decoded_scaled p t M cache scalar basis table htable,Sparse.denote_scale]

theorem denote_neg (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexponentialSAT.SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
    (entries : List (Index V × RingProgram.Code (Word (baseWidth p t)) d)) :
    Sparse.denote (decoded p t M cache scalar basis (scaled p t M cache table minusOne entries)) =
      -Sparse.denote (decoded p t M cache scalar basis entries) := by
  rw [decoded_neg p t M cache scalar basis table htable minusOne hminus,Sparse.denote_neg]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

end OAI.Algorithms
