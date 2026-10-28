import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintBetaServices

namespace OAI.Algorithms

/-! Concrete byte operations for the raw factor controller. The field view
only names physical work ports; every operation below has an actual trace. -/

namespace SubexponentialSAT.SubexpBlueprintPacking

open BitProgram StructuredCalls SubexpScanPrimitives SubexpBlueprintFactor
open SubexpBlueprintBetaServices

inductive Field where
  | input | origin | pointCopy | beta | negative | taylor | coefficients
  | argument | payload | scratch | parser | coordinate | row | factor
  deriving DecidableEq

def Field.port : Field → Fin 128
  | .input => 100 | .origin => 80 | .pointCopy => 81 | .beta => 77
  | .negative => 103 | .taylor => 104 | .coefficients => 105 | .argument => 106
  | .payload => 107 | .scratch => 108 | .parser => 109
  | .coordinate => 110 | .row => 111 | .factor => 112

def fieldValue : Field → Work → List Bool
  | .input, w => w.input | .origin, w => w.origin | .pointCopy, w => w.pointCopy
  | .beta, w => w.beta | .negative, w => w.negative | .taylor, w => w.taylor
  | .coefficients, w => w.coefficients | .argument, w => w.argument
  | .payload, w => w.payload | .scratch, w => w.scratch | .parser, w => w.parser
  | .coordinate, w => w.coordinate | .row, w => w.row | .factor, w => w.factor

def put : Field → List Bool → Work → Work
  | .input, x, w => {w with input := x}
  | .origin, x, w => {w with origin := x}
  | .pointCopy, x, w => {w with pointCopy := x}
  | .beta, x, w => {w with beta := x}
  | .negative, x, w => {w with negative := x}
  | .taylor, x, w => {w with taylor := x}
  | .coefficients, x, w => {w with coefficients := x}
  | .argument, x, w => {w with argument := x}
  | .payload, x, w => {w with payload := x}
  | .scratch, x, w => {w with scratch := x}
  | .parser, x, w => {w with parser := x}
  | .coordinate, x, w => {w with coordinate := x}
  | .row, x, w => {w with row := x}
  | .factor, x, w => {w with factor := x}

theorem work_ext {a b : Work} (h : ∀ f, fieldValue f a = fieldValue f b) : a = b := by
  cases a
  cases b
  congr 1 <;> first
    | exact h .input | exact h .origin | exact h .pointCopy | exact h .beta
    | exact h .negative | exact h .taylor | exact h .coefficients | exact h .argument
    | exact h .payload | exact h .scratch | exact h .parser | exact h .coordinate
    | exact h .row | exact h .factor

theorem Field.port_injective : Function.Injective Field.port := by
  intro f g h
  cases f <;> cases g <;> simp_all [Field.port]

@[simp] theorem fieldValue_put (f : Field) (x : List Bool) (w : Work) :
    fieldValue f (put f x w) = x := by cases f <;> rfl

@[simp] theorem put_self (f : Field) (w : Work) : put f (fieldValue f w) w = w := by
  cases f <;> rfl

@[simp] theorem put_put (f : Field) (x y : List Bool) (w : Work) :
    put f x (put f y w) = put f x w := by cases f <;> rfl

theorem fieldValue_put_ne (f g : Field) (hne : f ≠ g) (x : List Bool) (w : Work) :
    fieldValue f (put g x w) = fieldValue f w := by
  cases f <;> cases g <;> simp_all [fieldValue,put]

theorem put_comm (f g : Field) (hne : f ≠ g) (x y : List Bool) (w : Work) :
    put f x (put g y w) = put g y (put f x w) := by
  cases f <;> cases g <;> simp_all [put]

@[simp] theorem state_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work) (f : Field) :
    (state ctx regs w).stacks f.port = fieldValue f w := by
  cases f <;> rfl

@[simp] theorem state_regs (ctx : Context) (regs : Fin 8 → Bool) (w : Work) :
    (state ctx regs w).regs = regs := rfl

theorem state_put (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f : Field) (x : List Bool) :
    (state ctx regs (put f x w)).stacks =
      Function.update (state ctx regs w).stacks f.port x := by
  cases f <;> funext i <;> fin_cases i <;> rfl

theorem clear_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work) (f : Field) :
    Eval (clear f.port) (2*(fieldValue f w).length+3) (state ctx regs w)
      (state ctx (readRegs regs 0 1 none) (put f [] w)) := by
  have h : Eval (clear f.port) (2*((state ctx regs w).stacks f.port).length+3)
      (state ctx regs w)
      ⟨readRegs regs 0 1 none,StackRoutines.clearStacks f.port (state ctx regs w).stacks⟩ :=
    .call _ (ListRegisterProgram.clear_run f.port 0 1 regs (state ctx regs w).stacks)
  have he : (⟨readRegs regs 0 1 none,
      StackRoutines.clearStacks f.port (state ctx regs w).stacks⟩ : Data) =
      state ctx (readRegs regs 0 1 none) (put f [] w) := by
    apply state_ext
    · rfl
    · exact (state_put ctx (readRegs regs 0 1 none) w f []).symm
  simpa only [he,state_field] using h

theorem transfer_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f g : Field) (hne : f ≠ g) :
    Eval (transfer f.port g.port) (3*(fieldValue f w).length+3) (state ctx regs w)
      (state ctx (readRegs regs 0 1 none)
        (put g ((fieldValue f w).reverse ++ fieldValue g w) (put f [] w))) := by
  have hp : f.port ≠ g.port := fun h => hne (Field.port_injective h)
  have h : Eval (transfer f.port g.port) (3*((state ctx regs w).stacks f.port).length+3)
      (state ctx regs w)
      ⟨readRegs regs 0 1 none,StackRoutines.transferStacks f.port g.port (state ctx regs w).stacks⟩ :=
    .call _ (ListRegisterProgram.transfer_run f.port g.port 0 1 hp (by decide)
      regs (state ctx regs w).stacks)
  have he : (⟨readRegs regs 0 1 none,
      StackRoutines.transferStacks f.port g.port (state ctx regs w).stacks⟩ : Data) =
      state ctx (readRegs regs 0 1 none)
        (put g ((fieldValue f w).reverse ++ fieldValue g w) (put f [] w)) := by
    apply state_ext
    · rfl
    · rw [state_put,state_put]
      simp only [StackRoutines.transferStacks,state_field]
      rfl
  simpa only [he,state_field] using h

theorem push_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f : Field) (b : Bool) :
    Eval (pushBit f.port b) 2 (state ctx regs w)
      (state ctx (Function.update regs 0 b) (put f (b :: fieldValue f w) w)) := by
  let d := state ctx regs w
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 0 b) d))
    (Eval.base (StructuredProgram.Eval.atom (.push f.port 0)
      ((StructuredProgram.Atom.set (s := 128) 0 b).eval d)))
  have he : (⟨Function.update regs 0 b,
      Function.update (state ctx regs w).stacks f.port (b :: fieldValue f w)⟩ : Data) =
      state ctx (Function.update regs 0 b) (put f (b :: fieldValue f w) w) := by
    apply state_ext
    · rfl
    · exact (state_put ctx (Function.update regs 0 b) w f _).symm
  simpa only [pushBit,atom,d,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,
    Function.update_self,state_field,state_regs,he] using h

def parserEffect (d : Data) (v p : Bool) (input parser : List Bool) : Data :=
  ⟨Function.update (Function.update d.regs 0 v) 1 p,
    Function.update (Function.update d.stacks 100 input) 109 parser⟩

private def parserData (v p : Bool) (input parser : List Bool) : State 2 2 :=
  ⟨ParserProgram.pair v p,ParserProgram.pair input parser⟩

theorem parserRegs_injective : Function.Injective parserRegs := Fin.castAdd_injective _ _
theorem parserPorts_injective : Function.Injective parserPorts := by decide

theorem embed_parser (d : Data) (v p : Bool) (input parser : List Bool) :
    embedState parserRegs parserPorts d (parserData v p input parser) =
      parserEffect d v p input parser := by
  apply embedState_eq_of_ports _ _ _ _ _ parserRegs_injective parserPorts_injective
  · intro i
    fin_cases i <;> simp [parserEffect,parserRegs,parserData,ParserProgram.pair]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
    simp [parserEffect,h0,h1]
  · intro i
    fin_cases i <;> simp [parserEffect,parserPorts,parserData,ParserProgram.pair]
  · intro i hi
    have h100 : i ≠ 100 := fun h => hi ⟨0,h.symm⟩
    have h109 : i ≠ 109 := fun h => hi ⟨1,h.symm⟩
    simp [parserEffect,h100,h109]

theorem parserEffect_self (d : Data) :
    parserEffect d (d.regs 0) (d.regs 1) (d.stacks 100) (d.stacks 109) = d := by
  apply state_ext
  · simp [parserEffect]
  · simp [parserEffect]

theorem frame_eval (d : Data) (bits rest : List Bool)
    (hinput : d.stacks 100 = Encoding.frame bits ++ rest) (hparser : d.stacks 109 = []) :
    Eval (.call (ProgramLinking.liftProgram ParserProgram.frameProgram parserRegs parserPorts))
      (6*bits.length+4) d (parserEffect d false true rest bits.reverse) := by
  have ht := ParserProgram.frame_trace bits rest [] (d.regs 0) (d.regs 1)
  simp only [List.append_nil] at ht
  have h := eval_call_lifted ParserProgram.frameProgram parserRegs parserPorts d
    parserRegs_injective parserPorts_injective
    (a := parserData (d.regs 0) (d.regs 1) (Encoding.frame bits ++ rest) [])
    (b := parserData false true rest bits.reverse) ht
  simp only [embed_parser] at h
  rw [←hinput,←hparser,parserEffect_self] at h
  exact h

theorem unframe_eval (d : Data) (bits rest : List Bool)
    (hinput : d.stacks 100 = Encoding.frame bits ++ rest) (hparser : d.stacks 109 = []) :
    Eval unframe (9*bits.length+7) d (parserEffect d false false (bits ++ rest) []) := by
  have h := eval_call_lifted ParserProgram.unframeProgram parserRegs parserPorts d
    parserRegs_injective parserPorts_injective
    (a := parserData (d.regs 0) (d.regs 1) (Encoding.frame bits ++ rest) [])
    (b := parserData false false (bits ++ rest) [])
    (ParserProgram.unframe_trace bits rest (d.regs 0) (d.regs 1))
  simp only [embed_parser] at h
  rw [←hinput,←hparser,parserEffect_self] at h
  simpa only [unframe, hparser] using h

def frameEffect (d : Data) (src dst : Fin 128) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 true,
    Function.update d.stacks dst ((Encoding.frame (d.stacks src)).reverse ++ d.stacks dst)⟩

private def frameData (v p : Bool) (payload output : List Bool) : State 3 3 :=
  ⟨SubexpHornerProgram.triple v p true,SubexpHornerProgram.triple payload output []⟩

theorem frameRegs_injective : Function.Injective frameRegs := Fin.castAdd_injective _ _

theorem framePorts_injective (src dst : Fin 128)
    (hsd : src ≠ dst) (hs : src ≠ 108) (hd : dst ≠ 108) :
    Function.Injective (framePorts src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [framePorts]

theorem appendFrame_eval (src dst : Fin 128)
    (hsd : src ≠ dst) (hs : src ≠ 108) (hd : dst ≠ 108)
    (d : Data) (htmp : d.stacks 108 = []) :
    Eval (appendFrame src dst) (8*(d.stacks src).length+7) d (frameEffect d src dst) := by
  let set := (StructuredProgram.Atom.set (s := 128) 2 true).eval d
  have hset := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.set (s := 128) 2 true) d)
  have hp := framePorts_injective src dst hsd hs hd
  have hstart : embedState frameRegs (framePorts src dst) set
      (frameData (d.regs 0) (d.regs 1) (d.stacks src) (d.stacks dst)) = set := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective hp
    · intro i
      fin_cases i <;> simp [set,frameData,frameRegs,SubexpHornerProgram.triple,
        StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr]
    · intros; rfl
    · intro i
      fin_cases i <;> simp [set,frameData,framePorts,SubexpHornerProgram.triple,htmp,
        StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr]
    · intros; rfl
  have hend : embedState frameRegs (framePorts src dst) set
      (frameData false false (d.stacks src)
        ((Encoding.frame (d.stacks src)).reverse ++ d.stacks dst)) = frameEffect d src dst := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective hp
    · intro i
      fin_cases i <;> simp [frameEffect,frameData,frameRegs,SubexpHornerProgram.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
      simp [frameEffect,set,h0,h1,h2,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr]
    · intro i
      fin_cases i <;> simp [frameEffect,frameData,framePorts,SubexpHornerProgram.triple,
        hsd,hd.symm,htmp]
    · intro i hi
      have hdst : i ≠ dst := fun h => hi ⟨1,h.symm⟩
      simp [frameEffect,set,hdst,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr]
  have h := eval_call_lifted SubexpBlockAssembly.frameBody frameRegs (framePorts src dst) set
    frameRegs_injective hp
    (a := frameData (d.regs 0) (d.regs 1) (d.stacks src) (d.stacks dst))
    (b := frameData false false (d.stacks src)
      ((Encoding.frame (d.stacks src)).reverse ++ d.stacks dst))
    (SubexpBlockAssembly.frameBody_trace (d.stacks src) (d.stacks dst) (d.regs 0) (d.regs 1))
  rw [hstart,hend] at h
  have heval := Eval.seq hset h
  have hcost : 1 + (8 * (d.stacks src).length + 6) =
      8 * (d.stacks src).length + 7 := by omega
  rw [hcost] at heval
  exact heval

def afterFrameRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 0 false) 1 false) 2 true

theorem appendFrame_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f g : Field) (hne : f ≠ g) (hf : f ≠ .scratch) (hg : g ≠ .scratch)
    (htmp : w.scratch = []) :
    Eval (appendFrame f.port g.port) (8*(fieldValue f w).length+7) (state ctx regs w)
      (state ctx (afterFrameRegs regs)
        (put g ((Encoding.frame (fieldValue f w)).reverse ++ fieldValue g w) w)) := by
  have hfg : f.port ≠ g.port := fun h => hne (Field.port_injective h)
  have hfs : f.port ≠ 108 := fun h => hf (@Field.port_injective f .scratch h)
  have hgs : g.port ≠ 108 := fun h => hg (@Field.port_injective g .scratch h)
  have h := appendFrame_eval f.port g.port hfg hfs hgs (state ctx regs w) htmp
  have he : frameEffect (state ctx regs w) f.port g.port =
      state ctx (afterFrameRegs regs)
        (put g ((Encoding.frame (fieldValue f w)).reverse ++ fieldValue g w) w) := by
    apply state_ext
    · rfl
    · rw [state_put]
      simp only [frameEffect,state_field]
      rfl
  simpa only [state_field,he] using h

theorem capture_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f : Field) (hf : f ≠ .input) (hp : f ≠ .parser)
    (bits rest : List Bool) (hinput : w.input = Encoding.frame bits ++ rest)
    (hparser : w.parser = []) (hfield : fieldValue f w = []) :
    Eval (capture f.port) (9*bits.length+7) (state ctx regs w)
      (state ctx (readRegs regs 0 1 none) (put f bits (put .input rest w))) := by
  have h1 := frame_eval (state ctx regs w) bits rest hinput hparser
  let r1 := Function.update (Function.update regs 0 false) 1 true
  let w1 := put .parser bits.reverse (put .input rest w)
  have he1 : parserEffect (state ctx regs w) false true rest bits.reverse = state ctx r1 w1 := by
    apply state_ext
    · rfl
    · rw [state_put,state_put]
      rfl
  rw [he1] at h1
  have h2 := transfer_field ctx r1 w1 .parser f hp.symm
  have hv1 : fieldValue .parser w1 = bits.reverse := by simp [w1]
  have hvf : fieldValue f w1 = [] := by
    rw [fieldValue_put_ne f .parser hp,fieldValue_put_ne f .input hf]
    exact hfield
  have hw : put .parser [] w1 = put .input rest w := by
    change {w with input := rest, parser := []} = {w with input := rest}
    rw [←hparser]
  have hr : readRegs r1 0 1 none = readRegs regs 0 1 none := by
    funext i
    fin_cases i <;> simp [r1,readRegs]
  rw [hv1,hvf,List.reverse_reverse,List.append_nil,hw,hr] at h2
  simp only [List.length_reverse] at h2
  have h := Eval.seq h1 h2
  have hcost : 6 * bits.length + 4 + (3 * bits.length + 3) =
      9 * bits.length + 7 := by omega
  rw [hcost] at h
  exact h

@[simp] theorem afterFrameRegs_update_zero (regs : Fin 8 → Bool) (b : Bool) :
    afterFrameRegs (Function.update regs 0 b) = afterFrameRegs regs := by
  funext i
  fin_cases i <;> simp [afterFrameRegs]

@[simp] theorem afterFrameRegs_readRegs (regs : Fin 8 → Bool) :
    afterFrameRegs (readRegs regs 0 1 none) = afterFrameRegs regs := by
  funext i
  fin_cases i <;> simp [afterFrameRegs,readRegs]

@[simp] theorem readRegs_afterFrameRegs (regs : Fin 8 → Bool) :
    readRegs (afterFrameRegs regs) 0 1 none = afterFrameRegs regs := by
  funext i
  fin_cases i <;> simp [afterFrameRegs,readRegs]

def record (bits : List Bool) : List Bool := true :: Encoding.frame bits

theorem appendRecord_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f g : Field) (hne : f ≠ g) (hf : f ≠ .scratch) (hg : g ≠ .scratch)
    (htmp : w.scratch = []) :
    Eval (appendRecord f.port g.port) (8*(fieldValue f w).length+9) (state ctx regs w)
      (state ctx (afterFrameRegs regs)
        (put g ((record (fieldValue f w)).reverse ++ fieldValue g w) w)) := by
  have hp := push_field ctx regs w g true
  let w1 := put g (true :: fieldValue g w) w
  have hs : w1.scratch = [] := by
    change fieldValue .scratch (put g _ w) = []
    rw [fieldValue_put_ne .scratch g hg.symm]
    exact htmp
  have h := appendFrame_field ctx (Function.update regs 0 true) w1 f g hne hf hg hs
  have hv : fieldValue f w1 = fieldValue f w := fieldValue_put_ne f g hne _ w
  simp only [hv,w1,fieldValue_put,put_put,afterFrameRegs_update_zero] at h
  have hbytes : (Encoding.frame (fieldValue f w)).reverse ++ true :: fieldValue g w =
      (record (fieldValue f w)).reverse ++ fieldValue g w := by
    simp [record,List.reverse_cons,List.append_assoc]
  rw [hbytes] at h
  have heval := Eval.seq hp h
  have hcost : 2 + (8 * (fieldValue f w).length + 7) =
      8 * (fieldValue f w).length + 9 := by omega
  rw [hcost] at heval
  exact heval

theorem packComplete_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f g : Field) (hne : f ≠ g) (hfp : f ≠ .payload) (hgp : g ≠ .payload)
    (hfs : f ≠ .scratch) (hgs : g ≠ .scratch)
    (hp : w.payload = []) (hs : w.scratch = []) :
    Eval (packComplete f.port g.port) (13*(fieldValue f w).length+15) (state ctx regs w)
      (state ctx (afterFrameRegs regs)
        (put g ((record (fieldValue f w).reverse).reverse ++ fieldValue g w) (put f [] w))) := by
  have ht := transfer_field ctx regs w f .payload hfp
  change fieldValue .payload w = [] at hp
  rw [hp,List.append_nil] at ht
  let w1 := put .payload (fieldValue f w).reverse (put f [] w)
  let r1 := readRegs regs 0 1 none
  have hscratch : w1.scratch = [] := by
    change fieldValue .scratch (put .payload _ (put f [] w)) = []
    rw [fieldValue_put_ne .scratch .payload (by decide),
      fieldValue_put_ne .scratch f hfs.symm]
    exact hs
  have hr := appendRecord_field ctx r1 w1 .payload g hgp.symm (by decide) hgs hscratch
  have hvp : fieldValue .payload w1 = (fieldValue f w).reverse := by simp [w1]
  have hvg : fieldValue g w1 = fieldValue g w := by
    rw [fieldValue_put_ne g .payload hgp,fieldValue_put_ne g f hne.symm]
  rw [hvp,hvg] at hr
  let w2 := put g ((record (fieldValue f w).reverse).reverse ++ fieldValue g w) w1
  have hc := clear_field ctx (afterFrameRegs r1) w2 .payload
  have hv2 : fieldValue .payload w2 = (fieldValue f w).reverse := by
    rw [fieldValue_put_ne .payload g hgp.symm]
    exact hvp
  have hw : put .payload [] w2 =
      put g ((record (fieldValue f w).reverse).reverse ++ fieldValue g w) (put f [] w) := by
    unfold w2 w1
    rw [put_comm .payload g hgp.symm,put_put,put_comm .payload f hfp.symm]
    rw [←hp,put_self]
  rw [hv2,hw] at hc
  have h := Eval.seq ht (Eval.seq hr hc)
  simpa only [packComplete,Field.port,r1,afterFrameRegs_readRegs,readRegs_afterFrameRegs,
    List.length_reverse,show 3*(fieldValue f w).length+3+
      (8*(fieldValue f w).length+9+(2*(fieldValue f w).length+3))=
      13*(fieldValue f w).length+15 by omega] using h

theorem closeList_field (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (f g : Field) (hne : f ≠ g) (hfp : f ≠ .payload) (hgp : g ≠ .payload)
    (hfs : f ≠ .scratch) (hgs : g ≠ .scratch)
    (hp : w.payload = []) (hs : w.scratch = []) :
    Eval (closeList f.port g.port) (13*(fieldValue f w).length+30) (state ctx regs w)
      (state ctx (afterFrameRegs regs)
        (put g ((record (false :: fieldValue f w).reverse).reverse ++ fieldValue g w) (put f [] w))) := by
  have hpushed := push_field ctx regs w f false
  let w1 := put f (false :: fieldValue f w) w
  have hp1 : w1.payload = [] := by
    change fieldValue .payload (put f _ w) = []
    rw [fieldValue_put_ne .payload f hfp.symm]
    exact hp
  have hs1 : w1.scratch = [] := by
    change fieldValue .scratch (put f _ w) = []
    rw [fieldValue_put_ne .scratch f hfs.symm]
    exact hs
  have h := packComplete_field ctx (Function.update regs 0 false) w1 f g hne hfp hgp hfs hgs hp1 hs1
  simp only [w1,fieldValue_put,fieldValue_put_ne g f hne.symm,put_put,
    afterFrameRegs_update_zero,List.length_cons] at h
  have heval := Eval.seq hpushed h
  have hcost : 2 + (13 * ((fieldValue f w).length + 1) + 15) =
      13 * (fieldValue f w).length + 30 := by omega
  rw [hcost] at heval
  exact heval

end SubexponentialSAT.SubexpBlueprintPacking

end OAI.Algorithms
