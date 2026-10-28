import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CoreMaskProgram
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanScan
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 10 13
abbrev Code := Cmd 10 13
abbrev unary (n : ℕ) : List Bool := List.replicate n true
abbrev scopeBytes := SubexpIncidencePlanScan.scopeBytes
def scopeBits (scopes : List (List ℕ)) := Encoding.encodeList scopeBytes scopes

abbrev data (regs : Fin 10 → Bool)
    (source index vertex answer sourceCopy mask query pre tmp aux count codes payload : List Bool) :
    Data := ⟨regs, fun i => if i = 0 then source else if i = 1 then index else
    if i = 2 then vertex else if i = 3 then answer else if i = 4 then sourceCopy else
    if i = 5 then mask else if i = 6 then query else if i = 7 then pre else
    if i = 8 then tmp else if i = 9 then aux else if i = 10 then count else
    if i = 11 then codes else payload⟩

def idle (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) (answer : List Bool) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) answer [] [] [] [] [] [] [] [] []

abbrev seeded (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) []
    (scopeBits scopes) (unary e) [] [] [] [] [] [] []

def selected (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) []
    [] [] [] (scopeBits (scopes.take e)) [] [] [] [] []

def ready (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) []
    [] [] ((Encoding.encodeNat v).reverse) (scopeBits (scopes.take e)) [] [] [] [] []

def degree (scopes : List (List ℕ)) (e v : ℕ) : ℕ :=
  (Subexp.IncidencePlanSpec.incidenceFrom v 0 (scopes.take e)).length

def indices (scopes : List (List ℕ)) (e v : ℕ) : List Bool :=
  SubexpIncidencePlanScan.indexPrefix
    (Subexp.IncidencePlanSpec.incidenceFrom v 0 (scopes.take e)).reverse

def scanned (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) : Data :=
  data regs (scopeBits scopes) (unary e) (unary v) (unary (degree scopes e v))
    [] [] ((Encoding.encodeNat v).reverse) [] [] []
    (unary (scopes.take e).length) (indices scopes e v) []

theorem encode_map (scopes : List (List ℕ)) :
    Encoding.encodeList id (scopes.map scopeBytes) = scopeBits scopes := by
  induction scopes with
  | nil => rfl
  | cons C Cs ih =>
      simpa [scopeBits, Encoding.encodeList] using
        congrArg (fun tail => true :: (Encoding.frame (scopeBytes C) ++ tail)) ih

theorem select_prefix (records : List (List Bool)) (e : ℕ) :
    CoreMaskProgram.select (unary e) records = records.take e := by
  induction records generalizing e with
  | nil => simp [CoreMaskProgram.select]
  | cons x xs ih =>
      cases e with
      | zero => simpa [CoreMaskProgram.select, unary] using ih 0
      | succ e => simp [CoreMaskProgram.select, unary, List.replicate_succ, ih]

theorem prefix_length_le (scopes : List (List ℕ)) (e : ℕ) :
    (scopeBits (scopes.take e)).length ≤ (scopeBits scopes).length := by
  have h := CoreMaskProgram.selected_encoded_length_le (unary e) (scopes.map scopeBytes)
  simpa only [select_prefix, ← List.map_take, encode_map] using h

def copy (src dst : Fin 13) : Code := .call (StackRoutines.copyProgram src dst 8 0 1)
def copied (src dst : Fin 13) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

theorem copy_eval (src dst : Fin 13) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 8) (hd : (8 : Fin 13) ≠ dst) (ht : a.stacks 8 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst 8 0 1 hsd hs hd (by decide) a.regs a.stacks ht)

def push (dst : Fin 13) (bit : Bool) : Code :=
  .seq (.base (.atom (.set 0 bit))) (.base (.atom (.push dst 0)))
def pushed (dst : Fin 13) (bit : Bool) (a : Data) : Data :=
  ⟨Function.update a.regs 0 bit, Function.update a.stacks dst (bit :: a.stacks dst)⟩

theorem push_eval (dst : Fin 13) (bit : Bool) (a : Data) :
    Eval (push dst bit) 2 a (pushed dst bit a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) bit) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [push, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def prepare : Code := .seq (copy 0 4) (copy 1 5)

theorem prepare_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ rf, Eval prepare (7 * (scopeBits scopes).length + 7 * e + 10)
      (idle regs scopes e v []) (seeded rf scopes e v) := by
  let a := idle regs scopes e v []
  let b := copied 0 4 a
  let c := copied 1 5 b
  have h1 := copy_eval 0 4 a (by decide) (by decide) (by decide) rfl
  have h2 := copy_eval 1 5 b (by decide) (by decide) (by decide) rfl
  have hc : c = seeded c.regs scopes e v := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    fin_cases i <;> simp [ b, copied, a, idle, data, StackRoutines.copyStacks]
  refine ⟨c.regs, ?_⟩
  have h := h1.seq h2
  change Eval prepare _ a c at h
  rw [hc] at h
  have hlen0 : (a.stacks 0).length = (scopeBits scopes).length := rfl
  have hlen1 : (b.stacks 1).length = e := by
    change (List.replicate e true).length = e
    exact List.length_replicate
  have hcost : (7 * (scopeBits scopes).length + 5) + (7 * e + 5) =
      7 * (scopeBits scopes).length + 7 * e + 10 := by omega
  simpa only [hlen0, hlen1, hcost] using h

def maskReg (i : Fin 4) : Fin 10 := i.castAdd 6
def maskPort : Fin 4 → Fin 13 := ![4,5,6,7]
theorem maskReg_injective : Function.Injective maskReg := Fin.castAdd_injective _ _
theorem maskPort_injective : Function.Injective maskPort := by decide
def selectPrefix : Code := .call (ProgramLinking.liftProgram CoreMaskProgram.program maskReg maskPort)

noncomputable def maskResultRegs (regs : Fin 10 → Bool) : Fin 10 → Bool :=
  Function.extend maskReg (fun _ => false) regs

theorem mask_project (regs : Fin 10 → Bool) (source index vertex : List Bool) :
    projectState maskReg maskPort
      (data regs source index vertex [] source index [] [] [] [] [] [] []) =
      CoreMaskProgram.state (regs 0) (regs 1) (regs 2) (regs 3) source index [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem mask_embed (regs : Fin 10 → Bool) (source index vertex output : List Bool) :
    embedState maskReg maskPort
      (data regs source index vertex [] source index [] [] [] [] [] [] [])
      (CoreMaskProgram.state false false false false [] [] [] output) =
      data (maskResultRegs regs) source index vertex [] [] [] [] output [] [] [] [] [] := by
  apply embedState_eq_of_ports maskReg maskPort _ _ _ maskReg_injective maskPort_injective
  · intro i
    change Function.extend maskReg (fun _ => false) regs (maskReg i) = _
    rw [maskReg_injective.extend_apply]
    fin_cases i <;> rfl
  · intro i hi
    change Function.extend maskReg (fun _ => false) regs i = regs i
    exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h4 : i ≠ 4 := fun h => hi ⟨0, h.symm⟩
    have h5 : i ≠ 5 := fun h => hi ⟨1, h.symm⟩
    have h6 : i ≠ 6 := fun h => hi ⟨2, h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨3, h.symm⟩
    simp only [ ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7]

theorem select_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ)
    (he : e ≤ scopes.length) :
    ∃ n rf, n ≤ 10 * (scopeBits scopes).length + 10 ∧
      Eval selectPrefix n (seeded regs scopes e v) (selected rf scopes e v) := by
  let a := seeded regs scopes e v
  let b := CoreMaskProgram.state false false false false [] [] [] (scopeBits (scopes.take e))
  have hp : projectState maskReg maskPort a =
      CoreMaskProgram.state (regs 0) (regs 1) (regs 2) (regs 3)
        (Encoding.encodeList id (scopes.map scopeBytes) ++ []) (unary e) [] [] := by
    simpa only [a, seeded, data, encode_map, List.append_nil] using
      mask_project regs (scopeBits scopes) (unary e) (unary v)
  obtain ⟨n, hn, hr⟩ := CoreMaskProgram.run_correct (scopes.map scopeBytes) [] (unary e)
    (regs 0) (regs 1) (regs 2) (regs 3)
  have hb : CoreMaskProgram.state false false false false []
      ((unary e).drop (scopes.map scopeBytes).length) []
      (Encoding.encodeList id (CoreMaskProgram.select (unary e) (scopes.map scopeBytes))) = b := by
    simp [b, select_prefix, ← List.map_take, encode_map, unary, List.drop_replicate,
      Nat.sub_eq_zero_of_le he]
  rw [hb, ← hp] at hr
  have h := eval_call_from_state CoreMaskProgram.program maskReg maskPort a
    maskReg_injective maskPort_injective hr
  have hc : embedState maskReg maskPort a b =
      selected (maskResultRegs regs) scopes e v :=
    mask_embed regs (scopeBits scopes) (unary e) (unary v) (scopeBits (scopes.take e))
  refine ⟨n, maskResultRegs regs, ?_, ?_⟩
  · simpa [CoreMaskProgram.runtimeBound, encode_map] using hn
  · change Eval selectPrefix n a (embedState maskReg maskPort a b) at h
    rw [hc] at h
    exact h

def makeQuery : Code := .seq (copy 2 6) (push 6 false)

theorem query_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ rf, Eval makeQuery (7 * v + 7) (selected regs scopes e v) (ready rf scopes e v) := by
  let a := selected regs scopes e v
  let b := copied 2 6 a
  let c := pushed 6 false b
  have h1 := copy_eval 2 6 a (by decide) (by decide) (by decide) rfl
  have h2 := push_eval 6 false b
  have hc : c = ready c.regs scopes e v := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    fin_cases i <;>
      simp [ b, copied, a, selected, data, StackRoutines.copyStacks,
        Encoding.encodeNat, List.reverse_append]
  have h := h1.seq h2
  change Eval makeQuery _ a c at h
  rw [hc] at h
  have hlen : (a.stacks 2).length = v := by
    change (List.replicate v true).length = v
    exact List.length_replicate
  have hcost : (7 * v + 5) + 2 = 7 * v + 7 := by omega
  exact ⟨c.regs, by simpa only [hlen, hcost] using h⟩

def scanPort : Fin 10 → Fin 13 := ![4,5,6,8,9,10,7,11,12,3]
theorem scanPort_injective : Function.Injective scanPort := by decide
def scan : Code := liftCommand SubexpIncidencePlanScan.command 6 9 id scanPort

theorem scan_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ n rf, n ≤ 4 + SubexpIncidencePlanScan.scanBudget v 0 (scopes.take e) ∧
      Eval scan n (ready regs scopes e v) (scanned rf scopes e v) := by
  let a := ready regs scopes e v
  obtain ⟨n, rf, hr, _, _, _, hn⟩ :=
    SubexpIncidencePlanScan.command_eval (scopes.take e) regs v 0 0 [] []
  have hp : projectState id scanPort a =
      SubexpIncidencePlanScan.data regs v 0 (scopeBits (scopes.take e) ++ []) [] [] 0 := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [ scanPort, a, ready, data
        ]
  change Eval SubexpIncidencePlanScan.command n
    (SubexpIncidencePlanScan.data regs v 0 (scopeBits (scopes.take e) ++ []) [] [] 0) _ at hr
  rw [← hp] at hr
  have h := eval_liftCommand_from_state SubexpIncidencePlanScan.command 6 9 id scanPort a
    Function.injective_id scanPort_injective hr
  have hc : embedState id scanPort a
      (SubexpIncidencePlanScan.data rf v (0 + (scopes.take e).length) []
        (SubexpIncidencePlanScan.indexPrefix
          (Subexp.IncidencePlanSpec.incidenceFrom v 0 (scopes.take e)).reverse ++ []) []
        (0 + degree scopes e v)) = scanned rf scopes e v := by
    apply embedState_eq_of_ports id scanPort a _ _ Function.injective_id scanPort_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> simp [scanPort, scanned, data,
        SubexpIncidencePlanScan.data, degree, indices]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨9, h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨6, h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨5, h.symm⟩
      have h11 : i ≠ 11 := fun h => hi ⟨7, h.symm⟩
      simp only [scanned, a, ready, data, ite_eq_right h3, ite_eq_right h7, ite_eq_right h10, ite_eq_right h11]
  refine ⟨n + 1, rf, by omega, ?_⟩
  rw [← hc]
  exact h

def cleanupPorts : List (Fin 13) := [6,10,11]
def finish : Code := .seq (push 3 true) (WorkspaceCleanupProgram.command 0 1 cleanupPorts)

theorem finish_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ rf, Eval finish
      (2 + (2 * (v + 1 + (scopes.take e).length + (indices scopes e v).length) + 9))
      (scanned regs scopes e v) (idle rf scopes e v (unary (degree scopes e v + 1))) := by
  let a := scanned regs scopes e v
  let b := pushed 3 true a
  let c := WorkspaceCleanupProgram.finish 0 1 cleanupPorts b
  have h1 := push_eval 3 true a
  have h2 := WorkspaceCleanupProgram.command_eval 0 1 cleanupPorts (by decide) b
  have hc : c = idle c.regs scopes e v (unary (degree scopes e v + 1)) := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    change (WorkspaceCleanupProgram.finish 0 1 cleanupPorts b).stacks i = _
    rw [WorkspaceCleanupProgram.finish_stack]
    fin_cases i <;> simp [cleanupPorts,
      b, pushed, a, scanned, data, List.replicate_succ]
  have h := h1.seq h2
  change Eval finish _ a c at h
  rw [hc] at h
  refine ⟨c.regs, ?_⟩
  have hcost : WorkspaceCleanupProgram.cost cleanupPorts b =
      2 * (v + 1 + (scopes.take e).length + (indices scopes e v).length) + 9 := by
    simp [WorkspaceCleanupProgram.cost, cleanupPorts, b, pushed, a, scanned, data,
      Nat.add_assoc]
  simpa only [hcost] using h

def command : Code := .seq prepare (.seq selectPrefix (.seq makeQuery (.seq scan finish)))
def program := compiled command 0 3
def budget (scopes : List (List ℕ)) (e v : ℕ) : ℕ :=
  20 * (scopeBits scopes).length + 10 * e + 10 * v + 100 +
    SubexpIncidencePlanScan.scanBudget v 0 (scopes.take e) +
    2 * (scopes.take e).length + 2 * (indices scopes e v).length

theorem program_run (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ)
    (he : e ≤ scopes.length) :
    ∃ rf, RunsIn program (budget scopes e v)
      ((idle regs scopes e v []).withPC (some program.entry))
      ((idle rf scopes e v (unary (degree scopes e v + 1))).withPC none) := by
  obtain ⟨r1, h1⟩ := prepare_eval regs scopes e v
  obtain ⟨n2, r2, hn2, h2⟩ := select_eval r1 scopes e v he
  obtain ⟨r3, h3⟩ := query_eval r2 scopes e v
  obtain ⟨n4, r4, hn4, h4⟩ := scan_eval r3 scopes e v
  obtain ⟨r5, h5⟩ := finish_eval r4 scopes e v
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  refine ⟨r5, _, ?_, compiled_halt_trace h 0 3⟩
  dsimp [budget]
  omega

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
