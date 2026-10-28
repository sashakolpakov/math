import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOuterJobs
import OAI.Algorithms.SubexponentialSAT.SubexpExponentSourceProgram

namespace OAI.Algorithms

/-! Generate the actual bounded-degree exponent stream and feed it to the
fixed outer job loop.  The remaining source-service hypothesis is an actual
execution contract, to be instantiated by the current-exponent constructor. -/

namespace SubexponentialSAT.SubexpOuterJobSetup

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

def initializeOutput : Code := .base (.seq (.atom (.set 13 false))
  (.seq (.atom (.set 14 false)) (.seq (.atom (.set 15 false)) (.atom (.push 14 13)))))

def initialized (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 13 false) 14 false) 15 false,
    Function.update d.stacks 14 (false :: d.stacks 14)⟩

theorem initializeOutput_eval (d : Data) : Eval initializeOutput 4 d (initialized d) := by
  have h := (StructuredProgram.Eval.atom (.set (13 : Fin 16) false) d).seq
    ((StructuredProgram.Eval.atom (.set (14 : Fin 16) false) _).seq
      ((StructuredProgram.Eval.atom (.set (15 : Fin 16) false) _).seq
        (StructuredProgram.Eval.atom (.push (14 : Fin 128) (13 : Fin 16)) _)))
  exact .base (by simpa [initialized, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h)

def call (service : Code) : Code := .call (SubexpOuterJobs.program service)
def command (service : Code) : Code := .seq SubexpExponentSourceProgram.command
  (.seq initializeOutput (call service))
def program (service : Code) := compiled (command service) 2 14

def bound (D width T W : ℕ) : ℕ :=
  25 * (3 * D + 2) * (3 * D + 1).choose D + 17 * D + 29 +
    RecordPrograms.budget (SubexpOuterJobs.callbackCost D width T W)
      (SubexpOuterJobs.momentRecords D)

theorem exponent_output_eq (D : ℕ) :
    SubexpExponentSourceProgram.output D =
      Encoding.encodeList id (SubexpOuterJobs.momentRecords D) := by
  have h (xs : List (Fin D → ℕ)) :
      Encoding.encodeList SubexpExponentController.momentWord xs =
        Encoding.encodeList id (xs.map SubexpExponentController.momentWord) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [Encoding.encodeList, ih]
  exact h _

theorem program_runs (service : Code) (source : List Bool → List Bool)
    (D width T W : ℕ) (d : Data)
    (hc : SubexpOuterJobs.Context d D width)
    (spec : SubexpOuterJobs.SourceSpec service (SubexpOuterJobs.ValidMoment D) source T W d)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h14 : d.stacks 14 = []) (h111 : d.stacks 111 = [])
    (hwork : ∀ i ∈ SubexpExponentSourceProgram.work, d.stacks i = []) :
    ∃ e : Data, RunsIn (program service) (bound D width T W)
      (d.withPC (some (program service).entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 14
        (SubexpMomentProgram.input
          (SubexpOuterJobs.allJobs source D width (SubexpOuterJobs.momentRecords D)).reverse) := by
  obtain ⟨sn, s, hsn, hs, hss⟩ :=
    SubexpExponentSourceProgram.command_eval d D hc.dimension hwork
  let a := initialized s
  have ha := initializeOutput_eval s
  have hi : SubexpOuterJobs.Invariant d a := by
    constructor
    · intro i h0' h1' h14' h110' h111'
      simp [a, initialized, hss, h14', h110']
    · simp [a, initialized, hss, h0]
    · simp [a, initialized, hss, h1]
  have hout : a.stacks 14 = SubexpMomentProgram.input [] := by
    simp [a, initialized, hss, h14, SubexpMomentProgram.input, Encoding.encodeList]
  obtain ⟨inner, ⟨n, hn, ht⟩, hinv, houtput⟩ :=
    SubexpOuterJobs.moments_program_runs service source D width T W d hc spec a hi [] hout
  simp only [List.append_nil] at houtput
  have hstart : RecordPrograms.state SubexpOuterJobs.ports a false false false
      (Encoding.encodeList id (SubexpOuterJobs.momentRecords D)) [] = a := by
    apply RecordPrograms.state_eq_self
    · simp [a, initialized, SubexpOuterJobs.ports]
    · simp [a, initialized, SubexpOuterJobs.ports]
    · simp [a, initialized, SubexpOuterJobs.ports]
    · simp [a, initialized, hss, exponent_output_eq, SubexpOuterJobs.ports]
    · simp [a, initialized, hss, h111, SubexpOuterJobs.ports]
  rw [hstart] at ht
  let e := RecordPrograms.state SubexpOuterJobs.ports inner false true false [] []
  have he : Eval (call service) n a e := .call _ ht
  have total := hs.seq (ha.seq he)
  refine ⟨e, ⟨sn + (4 + n) + 1, ?_, compiled_halt_trace total 2 14⟩, ?_⟩
  · dsimp [bound]
    omega
  · funext i
    by_cases hi0 : i = 0
    · subst i; simp [e, RecordPrograms.state, SubexpOuterJobs.ports, hinv.xEmpty, h0]
    by_cases hi1 : i = 1
    · subst i; simp [e, RecordPrograms.state, SubexpOuterJobs.ports, hinv.sourceEmpty, h1]
    by_cases hi14 : i = 14
    · subst i; simpa [e, RecordPrograms.state, SubexpOuterJobs.ports] using houtput
    by_cases hi110 : i = 110
    · subst i
      simp [e, RecordPrograms.state, SubexpOuterJobs.ports, hwork 110 (by decide)]
    by_cases hi111 : i = 111
    · subst i; simp [e, RecordPrograms.state, SubexpOuterJobs.ports, h111]
    simpa [e, RecordPrograms.state, SubexpOuterJobs.ports, hi110, hi111, hi14] using
      hinv.frame i hi0 hi1 hi14 hi110 hi111

/-- The job order is the one already connected by permutation to the
coefficient-extraction jet formula. -/
theorem program_generated {D : ℕ} {C : Type*}
    (service : Code) (source : List Bool → List Bool)
    (encode : SymbolicCost.CoeffList D C → List Bool)
    (expression : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D C))
    (hsource : ∀ a ∈ Algorithm.exponentList D (2 * D + 1),
      source (SubexpExponentController.momentWord a) =
        SubexpPostfixControl.serializeCode encode (expression a).compile)
    (T W : ℕ) (d : Data)
    (hc : SubexpOuterJobs.Context d D (SubexpSymbolicCost.indexBits D))
    (spec : SubexpOuterJobs.SourceSpec service (SubexpOuterJobs.ValidMoment D) source T W d)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h14 : d.stacks 14 = []) (h111 : d.stacks 111 = [])
    (hwork : ∀ i ∈ SubexpExponentSourceProgram.work, d.stacks i = []) :
    ∃ e : Data, RunsIn (program service) (bound D (SubexpSymbolicCost.indexBits D) T W)
      (d.withPC (some (program service).entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 14
        (SubexpMomentProgram.input (SubexpQueryOrder.generatedJobs encode expression)) := by
  obtain ⟨e, he, hs⟩ := program_runs service source D (SubexpSymbolicCost.indexBits D) T W
    d hc spec h0 h1 h14 h111 hwork
  rw [SubexpOuterJobs.allJobs_generated source encode expression hsource] at hs
  exact ⟨e, he, hs⟩

theorem momentWord_length_le (D : ℕ) (bits : List Bool)
    (h : bits ∈ SubexpOuterJobs.momentRecords D) : bits.length ≤ 3 * D + 1 := by
  rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
  have ha' := (Algorithm.mem_exponentList D (2 * D + 1) a).mp (List.mem_reverse.mp ha)
  simp only [SubexpExponentController.momentWord, SubexpSymbolicCost.unaryWords_length_exact,
    List.sum_ofFn, List.length_ofFn]
  omega

def callbackBound (D width T W : ℕ) : ℕ :=
  T + D * (D + 1) * (100 * (5 * D + W + width + 3)) +
    13 * D ^ 2 + 46 * D + 21 * W + 49

theorem callbackCost_le (D width T W : ℕ) (bits : List Bool)
    (h : bits.length ≤ 3 * D + 1) :
    SubexpOuterJobs.callbackCost D width T W bits ≤ callbackBound D width T W := by
  calc
    _ ≤ T + 5 * (3 * D + 1) + D * (D + 1) *
        (100 * ((3 * D + 1) + W + 2 * D + width + 2)) +
        13 * D ^ 2 + 31 * D + 21 * W + 44 := by
      dsimp [SubexpOuterJobs.callbackCost]
      gcongr
    _ = callbackBound D width T W := by unfold callbackBound; ring

private theorem budget_le_of_bounds (cost : List Bool → ℕ) (records : List (List Bool))
    (L C : ℕ) (hlen : ∀ bits ∈ records, bits.length ≤ L)
    (hcost : ∀ bits ∈ records, cost bits ≤ C) :
    RecordPrograms.budget cost records ≤ records.length * (6 * L + C + 7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons bits rest ih =>
    have hl := hlen bits (by simp)
    have hc := hcost bits (by simp)
    have hr := ih (fun x hx => hlen x (by simp [hx])) (fun x hx => hcost x (by simp [hx]))
    simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The actual all-jobs loop has one non-polynomial factor: the number of
bounded-degree exponent vectors. Source time and length remain explicit. -/
theorem bound_le (D width T W : ℕ) :
    bound D width T W ≤ (3 * D + 1).choose D *
      (25 * (3 * D + 2) + callbackBound D width T W + 18 * D + 13) + 17 * D + 29 := by
  have hb := budget_le_of_bounds (SubexpOuterJobs.callbackCost D width T W)
    (SubexpOuterJobs.momentRecords D) (3 * D + 1) (callbackBound D width T W)
    (momentWord_length_le D)
    (fun bits h => callbackCost_le D width T W bits (momentWord_length_le D bits h))
  rw [SubexpOuterJobs.momentRecords_length] at hb
  unfold bound
  nlinarith

end SubexponentialSAT.SubexpOuterJobSetup

end OAI.Algorithms
