import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionStep

namespace OAI.Algorithms

/-!
# Physical support selection from packing metadata

Native inputs: unary D on 30, LE color on 31, unary position on 32,
metadata on 33, and unary r on 38. These five inputs are preserved.
Outputs 0 and 1 are ascending framed unary vertex lists for the requested
color and for the leftovers. Every other stack is empty at both boundaries.
-/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open BitProgram StructuredCalls SubexpScanPrimitives ConstructivePacking


def baseStacks (table : List Bool) (D t r : ℕ) (gBits : List Bool) : Fin 64 → List Bool :=
  fun j => if j = 30 then unary D else if j = 31 then gBits else if j = 32 then unary t
    else if j = 33 then table else if j = 38 then unary r else []

def inputState (regs : Fin 16 → Bool) (table : List Bool) (D t r : ℕ)
    (gBits : List Bool) : Data := ⟨regs, baseStacks table D t r gBits⟩

def outputState (table : List Bool) (D t r : ℕ) (gBits color outside : List Bool) : Data :=
  ⟨fun _ => false, Function.update (Function.update (baseStacks table D t r gBits) 0 color) 1 outside⟩

def preparedStacks (table : List Bool) (D t r : ℕ) (gBits : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (baseStacks table D t r gBits) 35 (unary (CounterPrograms.value gBits))) 39 (unary D))
      0 [false]) 1 [false]

def convertRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def convertPorts : Fin 3 → Fin 64 := ![40,35,41]

theorem convertRegs_injective : Function.Injective convertRegs := Fin.castAdd_injective 3 13
theorem convertPorts_injective : Function.Injective convertPorts := by decide

def convertColor : Code := .call
  (ProgramLinking.liftProgram CounterConversions.unaryProgram convertRegs convertPorts)

def setup : Code := .seq (copy 31 40) (.seq convertColor (.seq (copy 30 39)
  (.seq (TupleProgram.pushConst 0 0 false) (TupleProgram.pushConst 1 0 false))))

def loopPorts : UnaryForPrograms.Ports 16 64 := ⟨39,14,15⟩
def loop : Code := UnaryForPrograms.forCmd loopPorts visit
def finish : Code := .seq (clear 35) RegisterResetProgram.all

def command : Code := .seq setup (.seq loop finish)
def program := compiled command 30 0

def setupBound (D : ℕ) (gBits : List Bool) : ℕ :=
  CounterConversions.runtimeBound gBits + 7*gBits.length + 7*D + 14

def budget (L D t r : ℕ) (gBits : List Bool) : ℕ :=
  setupBound D gBits + D * (visitBound L D t r (CounterPrograms.value gBits) + 2) +
    2 * CounterPrograms.value gBits + 22

/-- A uniform polynomial in the physical table length, unary parameters,
requested color value, and its binary word length. -/
theorem budget_le_polynomial (L D t r : ℕ) (bits : List Bool) :
    budget L D t r bits ≤
      8000 * (L + D + t + r + CounterPrograms.value bits + bits.length + 1)^3 := by
  let s := L + D + t + r + CounterPrograms.value bits + bits.length + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hD : D ≤ s := by dsimp [s]; omega
  have ht : t ≤ s := by dsimp [s]; omega
  have hr : r ≤ s := by dsimp [s]; omega
  have hg : CounterPrograms.value bits ≤ s := by dsimp [s]; omega
  have hlen : bits.length ≤ s := by dsimp [s]; omega
  have hg1 : CounterPrograms.value bits + 1 ≤ s := by dsimp [s]; omega
  have hlen1 : bits.length + 1 ≤ s := by dsimp [s]; omega
  have hLD : L + D + 1 ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := by nlinarith
  have hs23 : s^2 ≤ s^3 := by
    calc
      s^2 = s^2 * 1 := (Nat.mul_one _).symm
      _ ≤ s^2 * s := Nat.mul_le_mul_left _ hs
      _ = s^3 := by simp [pow_succ]
  have hhead : SubexpHeadColorProgram.budget t r ≤ 82*s^2 := by
    unfold SubexpHeadColorProgram.budget
    calc
      t * (14*r+17) + 21*r + 30 ≤ s * (14*s+17) + 21*s + 30 := by gcongr
      _ ≤ 82*s^2 := by nlinarith
  have hp : prefixBound L D t r (CounterPrograms.value bits) ≤ 570*s^2 := by
    unfold prefixBound
    have hsq : (L+D+1)^2 ≤ s^2 := by gcongr
    nlinarith
  have hv : visitBound L D t r (CounterPrograms.value bits) ≤ 7440*s^2 := by
    unfold visitBound
    nlinarith
  have hsetup : setupBound D bits ≤ 60*s^2 := by
    unfold setupBound CounterConversions.runtimeBound
    have hprod : (CounterPrograms.value bits + 1) * (bits.length + 1) ≤ s^2 := by
      calc
        _ ≤ s*s := Nat.mul_le_mul hg1 hlen1
        _ = s^2 := by ring
    nlinarith
  have hloop : D * (visitBound L D t r (CounterPrograms.value bits)+2) ≤ 7442*s^3 := by
    calc
      _ ≤ s * (7442*s^2) := Nat.mul_le_mul hD (by nlinarith)
      _ = 7442*s^3 := by ring
  unfold budget
  change setupBound D bits + D * (visitBound L D t r (CounterPrograms.value bits)+2) +
    2 * CounterPrograms.value bits + 22 ≤ 8000*s^3
  nlinarith

theorem convertColor_eval (d : Data) (bits : List Bool)
    (h40 : d.stacks 40 = bits) (h35 : d.stacks 35 = []) (h41 : d.stacks 41 = []) :
    ∃ n e, n ≤ CounterConversions.runtimeBound bits ∧ Eval convertColor n d e ∧
      e.stacks = Function.update (Function.update d.stacks 40 []) 35
        (unary (CounterPrograms.value bits)) := by
  have ha : projectState convertRegs convertPorts d =
      CounterConversions.state (d.regs ∘ convertRegs) bits [] := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [projectState, convertPorts, CounterConversions.state, h40, h35, h41]
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs (d.regs ∘ convertRegs) bits []
  rw [← ha] at ht
  let b := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value bits) true ++ [])
  let e := embedState convertRegs convertPorts d b
  refine ⟨n, e, hn, eval_call_from_state _ _ _ _ convertRegs_injective convertPorts_injective ht, ?_⟩
  have hb : b.stacks = Function.update (Function.update
      (projectState convertRegs convertPorts d).stacks 0 []) 1
      (unary (CounterPrograms.value bits)) := by
    rw [ha]
    funext i
    fin_cases i <;> simp [b, CounterConversions.state]
  change Function.extend convertPorts b.stacks d.stacks = _
  rw [hb, ProgramLinking.extend_update convertPorts_injective,
    ProgramLinking.extend_update convertPorts_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project convertRegs convertPorts d convertRegs_injective convertPorts_injective)
  change Function.extend convertPorts (projectState convertRegs convertPorts d).stacks d.stacks = d.stacks at hp
  rw [hp]
  rfl

theorem setup_eval (regs : Fin 16 → Bool) (table : List Bool) (D t r : ℕ)
    (gBits : List Bool) :
    ∃ n e, n ≤ setupBound D gBits ∧ Eval setup n (inputState regs table D t r gBits) e ∧
      e.stacks = preparedStacks table D t r gBits := by
  let d := inputState regs table D t r gBits
  let a := afterCopy d 31 40 0 1
  have h1 : Eval (copy 31 40) (7*gBits.length+5) d a := by
    have he := copy_eval d 31 40 42 0 1 (by decide) (by decide) (by decide) (by decide) (by rfl)
    simpa [copy, a, d, inputState, baseStacks] using he
  obtain ⟨nc, b, hnc, hc, hsb⟩ := convertColor_eval a gBits
    (by simp [a, afterCopy, StackRoutines.copyStacks, d, inputState, baseStacks])
    (by simp [a, afterCopy, StackRoutines.copyStacks, d, inputState, baseStacks])
    (by simp [a, afterCopy, StackRoutines.copyStacks, d, inputState, baseStacks])
  let c := afterCopy b 30 39 0 1
  have h2 : Eval (copy 30 39) (7*D+5) b c := by
    have he := copy_eval b 30 39 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [hsb, a, afterCopy, StackRoutines.copyStacks, d, inputState, baseStacks])
    simpa [copy, c, hsb, a, afterCopy, StackRoutines.copyStacks, d, inputState, baseStacks] using he
  let f := TupleProgram.pushedState 0 0 false c
  let e := TupleProgram.pushedState 1 0 false f
  have h3 := TupleProgram.pushConst_eval (0 : Fin 64) (0 : Fin 16) false c
  have h4 := TupleProgram.pushConst_eval (1 : Fin 64) (0 : Fin 16) false f
  refine ⟨7*gBits.length+5 + (nc + (7*D+5 + (2+2))), e, ?_,
    h1.seq (hc.seq (h2.seq (h3.seq h4))), ?_⟩
  · unfold setupBound
    omega
  · funext j
    fin_cases j <;> simp [e, f, c, hsb, a, afterCopy,
      StackRoutines.copyStacks, d, inputState, baseStacks, preparedStacks]

theorem visitBound_mono {a b : ℕ} (hab : a ≤ b) (L t r g : ℕ) :
    visitBound L a t r g ≤ visitBound L b t r g := by
  unfold visitBound prefixBound
  gcongr

private theorem clean_after_outputs (d e : Data) (hc : Clean d) (left right : List Bool)
    (hs : e.stacks = Function.update (Function.update d.stacks 0 left) 1 right) : Clean e := by
  intro j hj
  have h0 : j ≠ 0 := by intro h; subst j; exact absurd hj (by decide)
  have h1 : j ≠ 1 := by intro h; subst j; exact absurd hj (by decide)
  simpa [hs, h0, h1] using hc j hj

variable {D r Q Δ : ℕ}

def metadataTable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) : List Bool :=
  SelectorProgram.rawRecords
    (PackingMetadata.records P (fun w => unary w.val) CollisionProgram.encodeType)

/-- The descending visits are actual evaluations of `visit`; no callback
execution is assumed in the final theorem. -/
theorem loop_visits (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g : ℕ) (n : ℕ) :
    ∀ d : Data, n ≤ D → d.stacks 33 = metadataTable P → d.stacks 32 = unary t.val →
      d.stacks 38 = unary r → d.stacks 35 = unary g → d.stacks 39 = unary n → Clean d →
    ∃ costs ticks e, UnaryForPrograms.Visits loopPorts visit costs ticks d e ∧
      ticks ≤ n * (visitBound (metadataTable P).length D t.val r g + 2) + 2 ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 39 [])
        0 (supportPrefix (colorTest P t g) n ++ d.stacks 0))
        1 (supportPrefix (outsideTest P) n ++ d.stacks 1) := by
  induction n with
  | zero =>
    intro d _ h33 h32 h38 h35 h39 hc
    refine ⟨[], 2, UnaryForPrograms.popped loopPorts d,
      .done d h39, by simp, ?_⟩
    funext j
    by_cases h0 : j = 0
    · subst j
      simp [UnaryForPrograms.popped, loopPorts, h39]
    by_cases h1 : j = 1
    · subst j
      simp [UnaryForPrograms.popped, loopPorts, h39]
    by_cases h39' : j = 39
    · subst j
      simp [UnaryForPrograms.popped, loopPorts, h39]
    · simp [UnaryForPrograms.popped, loopPorts, h0, h1, h39']
  | succ n ih =>
    intro d hnd h33 h32 h38 h35 h39 hc
    have hlt : n < D := by omega
    let p := UnaryForPrograms.popped loopPorts d
    have hp39 : p.stacks 39 = unary n := by
      simp [p, UnaryForPrograms.popped, loopPorts, h39, List.replicate_succ]
    have hp33 : p.stacks 33 = metadataTable P := by simp [p, UnaryForPrograms.popped, loopPorts, h33]
    have hp32 : p.stacks 32 = unary t.val := by simp [p, UnaryForPrograms.popped, loopPorts, h32]
    have hp38 : p.stacks 38 = unary r := by simp [p, UnaryForPrograms.popped, loopPorts, h38]
    have hp35 : p.stacks 35 = unary g := by simp [p, UnaryForPrograms.popped, loopPorts, h35]
    have hpc : Clean p := by
      intro j hj
      have hne : j ≠ 39 := by intro h; subst j; exact absurd hj (by decide)
      simpa [p, UnaryForPrograms.popped, loopPorts, hne] using hc j hj
    obtain ⟨nv, e, hnv, hev, hes⟩ := visit_eval P t g ⟨n,hlt⟩ p hp33 hp32 hp38 hp35 hp39 hpc
    have hnv' : nv ≤ visitBound (metadataTable P).length D t.val r g := by
      rw [hp33] at hnv
      exact hnv.trans (visitBound_mono (by omega) _ _ _ _)
    have he39 : e.stacks 39 = unary n := by simp [hes, hp39]
    obtain ⟨costs, nt, f, hv, hnt, hfs⟩ := ih e (by omega)
      (by simp [hes, hp33]) (by simp [hes, hp32]) (by simp [hes, hp38])
      (by simp [hes, hp35]) he39 (clean_after_outputs p e hpc _ _ hes)
    refine ⟨nv :: costs, nv+nt+2, f,
      .step (by simp [loopPorts, h39]) hev (by simp [hes, loopPorts, p]) hv, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · funext j
      by_cases h0 : j = 0
      · subst j
        cases hcolor : colorAt P t g ⟨n,hlt⟩ <;>
          simp [hfs, hes, p, UnaryForPrograms.popped, loopPorts, prefix_succ,
            colorTest, hlt, hcolor, List.append_assoc]
      by_cases h1 : j = 1
      · subst j
        cases hout : outsideAt P ⟨n,hlt⟩ <;>
          simp [hfs, hes, p, UnaryForPrograms.popped, loopPorts, prefix_succ,
            outsideTest, hlt, hout, List.append_assoc]
      by_cases h39' : j = 39
      · subst j
        simp [hfs]
      · simp [hfs, hes, p, UnaryForPrograms.popped, loopPorts, h0, h1, h39']

/-- The two output lists are computed from metadata; only raw parameter words
and the metadata table enter the fixed instruction program. -/
theorem program_run (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (gBits : List Bool) (regs : Fin 16 → Bool) :
    RunsIn program (budget (metadataTable P).length D t.val r gBits)
      ((inputState regs (metadataTable P) D t.val r gBits).withPC (some program.entry))
      ((outputState (metadataTable P) D t.val r gBits
        (Encoding.encodeList id (indexWords (colorTest P t (CounterPrograms.value gBits)) D))
        (Encoding.encodeList id (indexWords (outsideTest P) D))).withPC none) := by
  obtain ⟨ns, d, hns, hs, hsd⟩ := setup_eval regs (metadataTable P) D t.val r gBits
  have hdClean : Clean d := by
    intro j hj
    fin_cases j <;> first
    | exact absurd hj (by decide)
    | simp [hsd, preparedStacks, baseStacks]
  obtain ⟨costs, nl, e, hv, hnl, hse⟩ := loop_visits P t (CounterPrograms.value gBits) D d le_rfl
    (by simp [hsd, preparedStacks, baseStacks])
    (by simp [hsd, preparedStacks, baseStacks])
    (by simp [hsd, preparedStacks, baseStacks])
    (by simp [hsd, preparedStacks])
    (by simp [hsd, preparedStacks]) hdClean
  let f : Data := ⟨readRegs e.regs 0 1 none, Function.update e.stacks 35 []⟩
  have hf : Eval (clear 35) (2 * CounterPrograms.value gBits + 3) e f := by
    have h := TupleProgram.clear_eval (35 : Fin 64) (0 : Fin 16) 1 e
    simpa [clear, f, StackRoutines.clearStacks, hse, hsd, preparedStacks, baseStacks] using h
  have hz := RegisterResetProgram.all_eval f
  have hout : RegisterResetProgram.zeroed f = outputState (metadataTable P) D t.val r gBits
      (Encoding.encodeList id (indexWords (colorTest P t (CounterPrograms.value gBits)) D))
      (Encoding.encodeList id (indexWords (outsideTest P) D)) := by
    apply state_ext
    · rfl
    · funext j
      fin_cases j <;> simp [f, hse, hsd, outputState,
        preparedStacks, baseStacks, prefix_encode]
  rw [hout] at hz
  have he := hs.seq (hv.eval.seq (hf.seq hz))
  refine ⟨ns + (nl + (2 * CounterPrograms.value gBits + 3 + 16)) + 1, ?_,
    compiled_halt_trace he 30 0⟩
  unfold budget
  omega

theorem primitive_run (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (gBits : List Bool) (regs : Fin 16 → Bool) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * budget (metadataTable P).length D t.val r gBits)
      (primitiveCfg program
        ((inputState regs (metadataTable P) D t.val r gBits).withPC (some program.entry)))
      (primitiveCfg program
        ((outputState (metadataTable P) D t.val r gBits
          (Encoding.encodeList id (indexWords (colorTest P t (CounterPrograms.value gBits)) D))
          (Encoding.encodeList id (indexWords (outsideTest P) D))).withPC none)) :=
  primitive_execution program (program_run P t gBits regs)

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
