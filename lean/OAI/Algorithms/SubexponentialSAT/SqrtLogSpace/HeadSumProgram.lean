import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def cursorPorts : CounterForPrograms.Ports 40 896 where
  register := ⟨Fin.castAdd 37, by intro a b h; exact Fin.ext (congrArg (fun x : Fin 40 => x.val) h)⟩
  counter := 859
  scratch := 861
  counter_ne_scratch := by decide

def fuelPorts : CounterForPrograms.Ports 40 896 where
  register := ⟨Fin.castAdd 37, by intro a b h; exact Fin.ext (congrArg (fun x : Fin 40 => x.val) h)⟩
  counter := 860
  scratch := 861
  counter_ne_scratch := by decide

/-- The terminal cursor may have one overflow bit; it is never queried. -/
structure Cursor (h i : ℕ) (d : Data) : Prop where
  rank : value (d.stacks 859) = i
  fuel : value (d.stacks 860) + i = 2 ^ h
  fuelWidth : (d.stacks 860).length = h + 1
  wordWidth : (d.stacks 859).length ≤ h + 1
  activeWidth : i < 2 ^ h → (d.stacks 859).length = h
  scratch : d.stacks 861 = []

theorem Cursor.index_lt {h i : ℕ} {d : Data} (hc : Cursor h i d)
    (hp : 0 < value (d.stacks 860)) : i < 2 ^ h := by
  have := hc.fuel
  omega

theorem Cursor.word {h i : ℕ} {d : Data} (hc : Cursor h i d)
    (hp : 0 < value (d.stacks 860)) :
    d.stacks 859 = (Counters.wordEquiv h ⟨i, hc.index_lt hp⟩).val := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · exact (hc.activeWidth (hc.index_lt hp)).trans (Counters.wordEquiv h _).property.symm
  · change value (d.stacks 859) = value (ExecCNFTupleEnumeration.fixedBits h i)
    rw [ExecCNFTupleEnumeration.fixedBits_value h i (hc.index_lt hp)]
    exact hc.rank

theorem Cursor.initial (h : ℕ) (d : Data)
    (hw : d.stacks 859 = List.replicate h false)
    (hf : d.stacks 860 = List.replicate h false ++ [true]) (hs : d.stacks 861 = []) :
    Cursor h 0 d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hs⟩
  · simp [hw]
  · simpa [hf] using Counters.powerTwo_value h
  · simp [hf]
  · simp [hw]
  · intro _; simp [hw]

def body (accepted : Code) : Code :=
  .seq HeadEvaluationProgram.StagedGate.command
    (.seq (.ite 15 accepted (.base .skip)) (Counters.incrementCmd cursorPorts))

def command (accepted : Code) : Code := CounterForPrograms.forCmd fuelPorts (body accepted)

def program (accepted : Code) := compiled (command accepted) 859 853

theorem Cursor.advance {h i : ℕ} {d e : Data} (hc : Cursor h i d)
    (hp : 0 < value (d.stacks 860))
    (hw : e.stacks 859 = ripple true (d.stacks 859))
    (hf : e.stacks 860 = d.stacks 860) :
    Cursor h (i + 1) (CounterForPrograms.nextState fuelPorts e) := by
  have hi := hc.index_lt hp
  have hn : (CounterForPrograms.nextState fuelPorts e).stacks 860 =
      ripple false (e.stacks 860) := CounterForPrograms.nextState_counter fuelPorts e
  have hnext := CounterForPrograms.nextState_outside fuelPorts e 859 (by decide) (by decide)
  have hword : (CounterForPrograms.nextState fuelPorts e).stacks 859 =
      ripple true (d.stacks 859) := hnext.symm.trans hw
  have hlen : (d.stacks 859).length = h := hc.activeWidth hi
  have hpow : 2 ^ h < 2 ^ (h + 1) := by
    have := Nat.two_pow_pos h
    simp only [pow_succ]
    omega
  constructor
  · rw [hword, value_increment, hc.rank]
  · rw [hn, hf]
    have hv := value_decrement hp
    have := hc.fuel
    omega
  · rw [hn, hf, decrement_length hp]
    exact hc.fuelWidth
  · rw [hword]
    apply increment_length_le_of_lt
    · omega
    · rw [hc.rank]
      omega
  · intro hactive
    rw [hword, hc.word hp, Counters.increment_word _ hactive]
    exact (Counters.wordEquiv h _).property
  · exact CounterForPrograms.nextState_scratch fuelPorts e


def powerRegisters : Fin 3 → Fin 40 := Fin.castAdd 37

def powerStacks : Fin 2 → Fin 896 := ![861, 860]

def power : Code := .call (ProgramLinking.liftProgram
  Counters.powerTwoProgram powerRegisters powerStacks)

noncomputable def powerResult (d : Data) : Data :=
  embedState powerRegisters powerStacks d
    (CounterForPrograms.localData false false (d.regs 2) []
      (List.replicate (d.stacks 861).length false ++ [true]))

theorem power_eval (d : Data) (hf : d.stacks 860 = []) :
    Eval power (4 * (d.stacks 861).length + 5) d (powerResult d) := by
  have hr : Function.Injective powerRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective powerStacks := by decide
  have hp : projectState powerRegisters powerStacks d =
      CounterForPrograms.localData (d.regs 0) (d.regs 1) (d.regs 2)
        (d.stacks 861) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [powerStacks, counterStacks, hf]
  have ht := Counters.powerTwo_trace (d.stacks 861) (d.regs 0) (d.regs 1) (d.regs 2)
  rw [← hp] at ht
  exact eval_call_from_state Counters.powerTwoProgram powerRegisters powerStacks d hr hs ht

@[simp] theorem powerResult_fuel (d : Data) :
    (powerResult d).stacks 860 = List.replicate (d.stacks 861).length false ++ [true] :=
  embedState_stack powerRegisters powerStacks d _ (by decide) 1

@[simp] theorem powerResult_scratch (d : Data) : (powerResult d).stacks 861 = [] :=
  embedState_stack powerRegisters powerStacks d _ (by decide) 0

theorem powerResult_frame (d : Data) (j : Fin 896) (h0 : j ≠ 860) (h1 : j ≠ 861) :
    (powerResult d).stacks j = d.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  fin_cases i <;> simp_all [powerStacks]

open HeadEvaluationProgram.StagedGate (copy copyState copy_eval clear clearState clear_eval)

/-- The existing head preparation stores its actual zero word on651. Two
copies initialize cursor and binary-fuel construction; the head sum is reset. -/
def seed : Code := .seq (copy 651 859) (.seq (copy 651 861) (.seq power (clear 853)))

noncomputable def seeded (d : Data) : Data :=
  clearState (powerResult (copyState (copyState d 651 859) 651 861)) 853

theorem seed_eval (d : Data) (h : ℕ)
    (hshape : d.stacks 651 = List.replicate h false)
    (hfuel : d.stacks 860 = []) (hscratch : d.stacks 861 = [])
    (htemp : d.stacks 31 = []) :
    Eval seed (18 * h + 2 * (d.stacks 853).length + 18) d (seeded d) := by
  let d1 := copyState d 651 859
  let d2 := copyState d1 651 861
  have h1 := copy_eval d 651 859 (by decide) (by decide) (by decide) htemp
  have h2 := copy_eval d1 651 861 (by decide) (by decide) (by decide)
    (by simp [d1, copyState, StackRoutines.copyStacks, htemp])
  have h3 := power_eval d2 (by simp [d2, d1, copyState, StackRoutines.copyStacks, hfuel])
  have h4 := clear_eval (powerResult d2) 853
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  · rfl
  · simp [d2, d1, copyState, StackRoutines.copyStacks, hshape, hscratch,
      powerResult_frame _ _ (by decide : (853 : Fin 896) ≠ 860) (by decide)]
    omega
  · rfl

theorem seeded_stacks (d : Data) (h : ℕ)
    (hshape : d.stacks 651 = List.replicate h false)
    (hcursor : d.stacks 859 = []) (hscratch : d.stacks 861 = []) :
    (seeded d).stacks = Function.update (Function.update (Function.update d.stacks
      859 (List.replicate h false)) 860 (List.replicate h false ++ [true])) 853 [] := by
  funext j
  by_cases h853 : j = 853
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks]
  by_cases h860 : j = 860
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks, copyState,
      StackRoutines.copyStacks, hshape, hscratch]
  by_cases h861 : j = 861
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks, hscratch]
  simp [seeded, clearState, StackRoutines.clearStacks, h853, h860,
    powerResult_frame _ j h860 h861, copyState, StackRoutines.copyStacks, h861,
    hshape, hcursor]

theorem seeded_cursor (d : Data) (h : ℕ)
    (hshape : d.stacks 651 = List.replicate h false)
    (hcursor : d.stacks 859 = []) (hscratch : d.stacks 861 = []) :
    Cursor h 0 (seeded d) := by
  have hs := seeded_stacks d h hshape hcursor hscratch
  apply Cursor.initial
  · simp [hs]
  · simp [hs]
  · simp [hs, hscratch]


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram

/-- Addition consumes the assignment product directly at854. The two
coefficient scratch ports avoid the retained product zero/table caches. -/
def additionRegisters : Fin 8 → Fin 40 := Fin.castAdd 32

def additionStacks (i : Fin 28) : Fin 896 :=
  if i = 15 then 853 else if i = 27 then 854 else if i = 24 then 39
  else if i = 17 then 883 else if i = 22 then 884 else Fin.castAdd 868 i

theorem additionRegisters_injective : Function.Injective additionRegisters :=
  Fin.castAdd_injective _ _

theorem additionStacks_injective : Function.Injective additionStacks := by decide

def add : Code := .call (ProgramLinking.liftProgram Normalize.program
  additionRegisters additionStacks)

/-- The local projection uses the actual product idle layout left by the
factor interpreter; no array is copied and no layout service is assumed. -/
theorem addition_project (a : Data) (modulus width zero table degree uCap zCap : List Bool)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle modulus width zero table degree uCap zCap) i)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = []) :
    projectState additionRegisters additionStacks a =
      Normalize.state (a.regs ∘ additionRegisters) modulus width degree
        (a.stacks 853) (a.stacks 854) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    have hl := hlow (if i = 24 then 39 else Fin.castAdd 28 i)
    fin_cases i <;> first | rfl | exact hs0 | exact hs1 | exact hl

private theorem normalize_stacks_update (regs rr : Fin 8 → Bool)
    (modulus width degree seed source result : List Bool) :
    (Normalize.state rr modulus width degree result []).stacks =
      Function.update (Function.update
        (Normalize.state regs modulus width degree seed source).stacks 15 result) 27 [] := by
  funext i
  fin_cases i <;> rfl

/-- One concrete dense addition preserves every caller stack except the two
named arrays. Its local temporary growth is polynomial in their bounded size. -/
theorem add_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a : Data) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hp : projectState additionRegisters additionStacks a =
      Normalize.state (a.regs ∘ additionRegisters) M.bits width degree
        (Product.bytes seed) (Product.bytes source)) :
    let result := Normalize.run p t M cache source seed
    ∃ steps e, steps ≤ additionBudget n (baseWidth p t) d u J ∧
      Eval add steps a e ∧ Good ∅ u J result ∧
      e.stacks = Function.update (Function.update a.stacks 853 (Product.bytes result)) 854 [] := by
  dsimp only
  obtain ⟨steps, rr, hb, ht, hg, _⟩ := addition_run_space p t M cache source seed
    hsource hseed (a.regs ∘ additionRegisters) width degree hd hw
  rw [← hp] at ht
  let e := embedState additionRegisters additionStacks a
    (Normalize.state rr M.bits width degree (Product.bytes (Normalize.run p t M cache source seed)) [])
  refine ⟨steps, e, hb, eval_call_from_state Normalize.program additionRegisters
    additionStacks a additionRegisters_injective additionStacks_injective ht, hg, ?_⟩
  have hs := normalize_stacks_update (a.regs ∘ additionRegisters) rr M.bits width degree
    (Product.bytes seed) (Product.bytes source) (Product.bytes (Normalize.run p t M cache source seed))
  have hproject := congrArg StructuredProgram.State.stacks hp
  change Function.extend additionStacks
    (Normalize.state rr M.bits width degree
      (Product.bytes (Normalize.run p t M cache source seed)) []).stacks a.stacks = _
  rw [hs, ← hproject, ProgramLinking.extend_update additionStacks_injective,
    ProgramLinking.extend_update additionStacks_injective]
  change Function.update (Function.update
    (embedState additionRegisters additionStacks a
      (projectState additionRegisters additionStacks a)).stacks
    853 (Product.bytes (Normalize.run p t M cache source seed))) 854 [] = _
  rw [embedState_project additionRegisters additionStacks a
    additionRegisters_injective additionStacks_injective]


/-- Accepted factors are added and their reusable arithmetic workspace is
reclaimed before the controller increments its candidate word. -/
def accumulate : Code := .seq add FactorEnvironment.reset

theorem accumulate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a : Data) (width degree zero table uCap zCap : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
    (hseedWord : a.stacks 853 = Product.bytes seed)
    (hsourceWord : a.stacks 854 = Product.bytes source)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = []) :
    let result := Normalize.run p t M cache source seed
    let budget := additionBudget n (baseWidth p t) d u J + FactorEnvironment.resetCost a
    ∃ steps e, steps ≤ budget ∧ Eval accumulate steps a e ∧ Good ∅ u J result ∧
      e.stacks = Function.update (Function.update (FactorEnvironment.resetResult a).stacks
        853 (Product.bytes result)) 854 [] ∧
      (∀ i : Fin 56, e.stacks (Fin.castAdd 840 i) = []) ∧
      ∀ q z, q ≤ steps + 1 → Trace (compiled accumulate 854 853) q
        (a.withPC (some (compiled accumulate 854 853).entry)) z →
        dataBits z ≤ stackBits a.stacks + budget + 1 := by
  dsimp only
  have hp := addition_project a M.bits width zero table degree uCap zCap hlow hs0 hs1
  rw [hseedWord, hsourceWord] at hp
  obtain ⟨steps, e, hb, he, hg, hs⟩ := add_eval p t M cache source seed hsource hseed
    a width degree hd hw hp
  have henv : FactorEnvironment.resetCost e = FactorEnvironment.resetCost a := by
    simp [FactorEnvironment.resetCost, FactorEnvironment.environmentPorts,
      SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, projectState, hs]
  have hframe : (FactorEnvironment.resetResult e).stacks =
      Function.update (Function.update (FactorEnvironment.resetResult a).stacks
        853 (Product.bytes (Normalize.run p t M cache source seed))) 854 [] := by
    funext i
    rw [FactorEnvironment.reset_stacks, hs]
    by_cases h853 : i = 853
    · subst i; simp [FactorEnvironment.environmentPorts]
    by_cases h854 : i = 854
    · subst i; simp [FactorEnvironment.environmentPorts]
    simp [h853, h854, FactorEnvironment.reset_stacks]
  have hlowe : ∀ i : Fin 56, e.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i := by
    intro i
    have h853 : Fin.castAdd 840 i ≠ (853 : Fin 896) := by
      intro h; have hx : i.val = 853 := congrArg Fin.val h; have := i.isLt; omega
    have h854 : Fin.castAdd 840 i ≠ (854 : Fin 896) := by
      intro h; have hx : i.val = 854 := congrArg Fin.val h; have := i.isLt; omega
    simpa [hs, h853, h854] using hlow i
  refine ⟨steps + FactorEnvironment.resetCost e, FactorEnvironment.resetResult e,
    by omega, he.seq (FactorEnvironment.reset_eval e), hg, hframe, ?_, ?_⟩
  · intro i
    rw [FactorEnvironment.reset_stacks, hlowe]
    fin_cases i <;> rfl
  intro q z hq hz
  have ht := trace_dataBits (compiled accumulate 854 853) hz
  change dataBits z ≤ stackBits a.stacks + q at ht
  omega


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

/-- The tested value uses every integer-signature component and local correction bit. -/
def gateValue (a : Data) (rows : List (List (List Bool))) : Bool :=
  decide (signatureValue (a.stacks 864) (a.stacks 859) rows = a.stacks 866) &&
    LeafWeightProgram.good (a.stacks 859) (a.stacks 867) (a.stacks 868)

def bodyBudget (a : Data) (rows : List (List (List Bool))) (acceptedCost : ℕ) : ℕ :=
  HeadEvaluationProgram.HeadGate.budget (a.stacks 864) (a.stacks 859) rows (a.stacks 866) +
    9 * HeadEvaluationProgram.StagedGate.sourceLength a + acceptedCost +
    8 * (a.stacks 859).length + 58

/-- Compose the real gate, the selected branch, and the real ripple increment.
The branch contract is an internal composition rule; the final scan instantiates
it with the named assignment-factor and dense-add commands. -/
theorem body_eval (accepted : Code) (a : Data) (rows : List (List (List Bool)))
    (C : ℕ) (P : Data → Prop)
    (hclean : ∀ i : Fin 32, a.stacks (HeadEvaluationProgram.StagedGate.stackMap i) = [])
    (hmatrix : a.stacks 865 = words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length = (a.stacks 859).length)
    (hE : (a.stacks 859).length = (a.stacks 867).length)
    (hH : (a.stacks 859).length = (a.stacks 868).length)
    (hs : a.stacks 861 = [])
    (haccepted : gateValue a rows = true → ∀ out : Fin 40 → Bool, out 15 = true →
      ∃ nb b, nb ≤ C ∧ Eval accepted nb ⟨out, a.stacks⟩ b ∧
        b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
        b.stacks 861 = [] ∧ P b)
    (hrejected : gateValue a rows = false → ∀ out : Fin 40 → Bool, P ⟨out, a.stacks⟩) :
    ∃ steps b, steps ≤ bodyBudget a rows C ∧
      Eval (body accepted) steps a (Counters.incrementResult cursorPorts b) ∧
      b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
      b.stacks 861 = [] ∧ P b := by
  obtain ⟨ng, hng, out, hg, hv⟩ := HeadEvaluationProgram.StagedGate.command_eval
    a rows hclean hmatrix hlen hE hH
  change out 15 = gateValue a rows at hv
  have hbranch : ∃ nb b, nb ≤ C ∧
      Eval (.ite 15 accepted (.base .skip)) (nb + 1) ⟨out, a.stacks⟩ b ∧
      b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
      b.stacks 861 = [] ∧ P b := by
    cases hh : out 15 with
    | false =>
        refine ⟨0, ⟨out, a.stacks⟩, Nat.zero_le C,
          .ite_false hh (.base (.skip _)), rfl, rfl, hs, ?_⟩
        exact hrejected (hv.symm.trans hh) out
    | true =>
        obtain ⟨nb, b, hb, he, hc, hf, hbs, hp⟩ := haccepted (hv.symm.trans hh) out hh
        exact ⟨nb, b, hb, .ite_true hh he, hc, hf, hbs, hp⟩
  obtain ⟨nb, b, hb, he, hc, hf, hbs, hp⟩ := hbranch
  have hi := Counters.increment_eval cursorPorts b hbs
  refine ⟨ng + (nb + 1 + (rippleCost true (b.stacks 859) + 1)), b, ?_,
    hg.seq (he.seq hi), hc, hf, hbs, hp⟩
  have hr := rippleCost_le true (b.stacks 859)
  rw [hc] at hr
  dsimp only [bodyBudget]
  rw [hc]
  omega

/-- The counter interface sees the exact next index even after the last word
has overflowed; the overflow word is excluded from further callbacks. -/
theorem body_cursor_next {h i : ℕ} {a b : Data} (hc : Cursor h i a)
    (hp : 0 < value (a.stacks 860))
    (hw : b.stacks 859 = a.stacks 859) (hf : b.stacks 860 = a.stacks 860)
    (hs : b.stacks 861 = []) :
    Cursor h (i + 1) (CounterForPrograms.nextState fuelPorts
      (Counters.incrementResult cursorPorts b)) := by
  apply hc.advance hp
  · rw [show (Counters.incrementResult cursorPorts b).stacks 859 =
        ripple true (b.stacks 859) from Counters.incrementResult_counter cursorPorts b, hw]
  · rw [Counters.incrementResult_stacks cursorPorts b hs]
    simpa [cursorPorts] using hf


/-- The mathematical output recurrence keeps only the current accumulator.
It specifies the native counted scan, and is not an executable assignment list. -/
def fold (visit : ℕ → List Bool → List Bool) : ℕ → List Bool → List Bool
  | 0, initial => initial
  | i + 1, initial => visit i (fold visit i initial)

/-- Output correctness for the actual indexed head loop. The step premise is
instantiated by body_eval and the concrete accepted-factor composition. -/
theorem command_fold (accepted : Code) (visit : ℕ → List Bool → List Bool)
    (I : ℕ → Data → Prop) (cost : ℕ → ℕ)
    (spec : ∀ i a, I i a → a.stacks 861 = [] → 0 < value (a.stacks 860) →
      ∃ nb b, nb ≤ cost i ∧ Eval (body accepted) nb a b ∧
        b.stacks 860 = a.stacks 860 ∧ b.stacks 861 = [] ∧
        I (i + 1) (CounterForPrograms.nextState fuelPorts b) ∧
        b.stacks 853 = visit i (a.stacks 853))
    (a : Data) (hs : a.stacks 861 = [])
    (hi : I 0 (CounterForPrograms.testResult fuelPorts a)) :
    ∃ costs steps e, Eval (command accepted) steps a e ∧
      (∃ loopSteps, CounterForPrograms.Visits fuelPorts (body accepted) costs loopSteps
        (CounterForPrograms.testResult fuelPorts a) e ∧
        steps = 8 * (a.stacks 860).length + 7 + loopSteps) ∧
      I (value (a.stacks 860)) e ∧
      e.stacks 853 = fold visit (value (a.stacks 860)) (a.stacks 853) ∧
      value (e.stacks 860) = 0 ∧ (e.stacks 860).length = (a.stacks 860).length ∧
      e.stacks 861 = [] ∧ costs.sum ≤ CounterForPrograms.budgetSum cost 0 (value (a.stacks 860)) ∧
      steps ≤ costs.sum + (value (a.stacks 860) + 1) * (16 * (a.stacks 860).length + 16) := by
  let J := fun i d => I i d ∧ d.stacks 853 = fold visit i (a.stacks 853)
  have hstep : ∀ i d, J i d → d.stacks fuelPorts.scratch = [] →
      0 < value (d.stacks fuelPorts.counter) →
      ∃ nb e, nb ≤ cost i ∧ Eval (body accepted) nb d e ∧
        e.stacks fuelPorts.counter = d.stacks fuelPorts.counter ∧
        e.stacks fuelPorts.scratch = [] ∧
        J (i + 1) (CounterForPrograms.nextState fuelPorts e) := by
    intro i d hd hds hp
    obtain ⟨nb, e, hb, he, hc, hes, hI, hout⟩ := spec i d hd.1 hds hp
    refine ⟨nb, e, hb, he, hc, hes, hI, ?_⟩
    have hn := CounterForPrograms.nextState_outside fuelPorts e 853 (by decide) (by decide)
    rw [← hn, hout, hd.2]
    rfl
  have hstart : J 0 (CounterForPrograms.testResult fuelPorts a) := by
    refine ⟨hi, ?_⟩
    rw [CounterForPrograms.testResult_stacks fuelPorts a hs]
    rfl
  obtain ⟨costs, steps, e, he, hvis, _, hI, hz, hw, hes, hb, ht⟩ :=
    CounterLoops.for_correct_measured_next fuelPorts (body accepted) J cost hstep a hs hstart
  exact ⟨costs, steps, e, he, hvis, hI.1, hI.2, hz, hw, hes, hb, ht⟩

open scoped BigOperators

/-- A valid additive accumulator decodes to the exact sum of all visited
contributions, with no retained family of previous states. -/
theorem fold_decode_sum {R : Type*} [AddCommMonoid R]
    (visit : ℕ → List Bool → List Bool) (decode : List Bool → R)
    (valid : List Bool → Prop) (contribution : ℕ → R) (initial : List Bool) (N : ℕ)
    (hi : valid initial)
    (step : ∀ i < N, ∀ a, valid a → valid (visit i a) ∧
      decode (visit i a) = decode a + contribution i) :
    valid (fold visit N initial) ∧
      decode (fold visit N initial) = decode initial + ∑ i ∈ Finset.range N, contribution i := by
  induction N with
  | zero => simpa [fold] using hi
  | succ N ih =>
      obtain ⟨hv, he⟩ := ih (fun i h a ha => step i (by omega) a ha)
      obtain ⟨hv', he'⟩ := step N (by omega) _ hv
      refine ⟨hv', ?_⟩
      simpa [fold, he, Finset.sum_range_succ, add_assoc] using he'

/-- Numeric bit-counter order covers every head assignment exactly once. -/
theorem range_sum_eq_assignments {R : Type*} [AddCommMonoid R]
    (h : ℕ) (f : (Fin h → Bool) → R) :
    (∑ i ∈ Finset.range (2 ^ h), if hi : i < 2 ^ h then
      f (AttainedSignatures.assignmentEquiv h ⟨i, hi⟩) else 0) =
      ∑ a : Fin h → Bool, f a := by
  rw [Finset.sum_range]
  have hh := (AttainedSignatures.assignmentEquiv h).sum_comp f
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]


/-- Dense addition's local working set is independent of the retained caller
frame. The physical input cap P is supplied by the bounded arrays and caches. -/
theorem add_prefix (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J P B steps : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a e : Data) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hp : projectState additionRegisters additionStacks a =
      Normalize.state (a.regs ∘ additionRegisters) M.bits width degree
        (Product.bytes seed) (Product.bytes source))
    (hinput : ∀ j, (a.stacks (additionStacks j)).length ≤ P)
    (hframe : ∀ j, (a.stacks j).length ≤ B)
    (hbudget : 28 * P + additionBudget n (baseWidth p t) d u J ≤ B)
    (he : Eval add steps a e) :
    ∀ q z, q ≤ steps → Trace (compiled add 854 853) q
      (a.withPC (some (compiled add 854 853).entry)) z →
      ∀ j, (z.stacks j).length ≤ B := by
  obtain ⟨nt, rr, _, ht, _, hspace⟩ := addition_run_space p t M cache source seed
    hsource hseed (a.regs ∘ additionRegisters) width degree hd hw
  rw [← hp] at ht hspace
  have hsmall : dataBits ((projectState additionRegisters additionStacks a).withPC
      (some Normalize.program.entry)) ≤ 28 * P :=
    StreamResources.dataBits_le_mul _ hinput
  have hlocal : ∀ q z, q ≤ nt → Trace Normalize.program q
      ((projectState additionRegisters additionStacks a).withPC
        (some Normalize.program.entry)) z → ∀ j, (z.stacks j).length ≤ B := by
    intro q z hq hz j
    exact (hspace q z hq hz j).trans (by omega)
  have hcall := eval_call_from_state Normalize.program additionRegisters additionStacks a
    additionRegisters_injective additionStacks_injective ht
  have htime := StreamResources.eval_steps_eq 854 853 he hcall
  subst steps
  have hglobal := StructuredSpace.liftProgram_stack_bound Normalize.program
    additionRegisters additionStacks (a.withPC none) additionRegisters_injective
    additionStacks_injective ht hlocal hframe
  have hinit : ProgramLinking.embedCfg additionRegisters additionStacks id none (a.withPC none)
      ((projectState additionRegisters additionStacks a).withPC (some Normalize.program.entry)) =
      a.withPC (some (ProgramLinking.liftProgram Normalize.program additionRegisters
        additionStacks).entry) := by
    change (embedState additionRegisters additionStacks a
      (projectState additionRegisters additionStacks a)).withPC _ = _
    rw [embedState_project additionRegisters additionStacks a
      additionRegisters_injective additionStacks_injective]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases hcall with
  | call prog htrace =>
      exact StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site add 854 853) htrace hglobal

/-- The actual numeric cursor denotes the assignment used by the full-key gate. -/
theorem Cursor.assignment_word {h i : ℕ} {a : Data} (hc : Cursor h i a)
    (hp : 0 < value (a.stacks 860)) :
    a.stacks 859 = List.ofFn (AttainedSignatures.assignmentEquiv h ⟨i, hc.index_lt hp⟩) := by
  rw [AttainedSignatures.assignment_word]
  exact hc.word hp

/-- With the staged local E mask and all-one local head mask, the actual gate
is exactly the full integer-signature fiber restriction. -/
theorem cursor_gate_iff {h d i : ℕ} {a : Data} (hcursor : Cursor h i a)
    (hp : 0 < value (a.stacks 860))
    (W : List Bool) (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (representative : Fin h → Bool) (E : Finset (Fin h))
    (hc : ∀ j v, (BinaryArithmetic.toNat (c j v) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) + A j v)
    (hW : a.stacks 864 = W)
    (hkey : a.stacks 866 = signatureValue W (List.ofFn representative)
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = LeafWeightProgram.supportBits ⟨E⟩)
    (hH : a.stacks 868 = List.replicate h true) :
    gateValue a (List.ofFn (fun j => List.ofFn (c j))) = true ↔
      LayoutSignatureBound.boolSignature A
        (AttainedSignatures.assignmentEquiv h ⟨i, hcursor.index_lt hp⟩) =
          LayoutSignatureBound.boolSignature A representative ∧
      ∀ v ∈ E, AttainedSignatures.assignmentEquiv h ⟨i, hcursor.index_lt hp⟩ v = true := by
  have hg := HeadEvaluationProgram.HeadGate.flag_exact_iff W c A
    (AttainedSignatures.assignmentEquiv h ⟨i, hcursor.index_lt hp⟩)
    representative hc E (fun _ => ()) ()
  simpa [gateValue, hcursor.assignment_word hp, hW, hkey, hE, hH,
    LeafWeightProgram.headBits] using hg


/-- The local addition cap follows from the physical caches and the proved
polynomial encoded-array bound, independently of the caller's frame bound. -/
theorem addition_input_length_le (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {n d u J P : ℕ}
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a : Data) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hp : projectState additionRegisters additionStacks a =
      Normalize.state (a.regs ∘ additionRegisters) M.bits width degree
        (Product.bytes seed) (Product.bytes source))
    (hmod : M.bits.length ≤ P) (hwidth : baseWidth p t ≤ P) (hdegree : d ≤ P)
    (harray : u * J * (2 * (u + J + n) + 2 * (d * baseWidth p t) + 2) ≤ P) :
    ∀ j, (a.stacks (additionStacks j)).length ≤ P := by
  have hsourceSize := (empty_bytes_length_le hsource).trans harray
  have hseedSize := (empty_bytes_length_le hseed).trans harray
  have hwidthSize := hw.le.trans hwidth
  have hdegreeSize := hd.le.trans hdegree
  intro j
  have hj := congrFun (congrArg StructuredProgram.State.stacks hp) j
  change a.stacks (additionStacks j) = _ at hj
  rw [hj]
  fin_cases j <;> dsimp [Normalize.state, Normalize.extend, Dictionary.machine,
    Dictionary.outputTape, Dictionary.tapes, Fin.snoc, Fin.castPred, Fin.castLT]
  all_goals first | exact Nat.zero_le P | exact hmod | exact hsourceSize |
    exact hseedSize | exact hwidthSize | exact hdegreeSize


private theorem clearMany_prefix {S steps B : ℕ} (ports : List (Fin S)) (port : Fin S)
    {a b : State 16 S} (he : Eval (SubexpSetupStorage.clearMany ports) steps a b)
    (hframe : ∀ j, (a.stacks j).length ≤ B) :
    ∀ q z, q ≤ steps → Trace (compiled (SubexpSetupStorage.clearMany ports) port port) q
      (a.withPC (some (compiled (SubexpSetupStorage.clearMany ports) port port).entry)) z →
      ∀ j, (z.stacks j).length ≤ B := by
  induction ports generalizing steps a b with
  | nil =>
      cases he with
      | base hb =>
          cases hb with
          | skip =>
              intro q z hq hz
              have hzero : q = 0 := by omega
              subst q
              cases hz
              exact hframe
  | cons p ps ih =>
      cases he with
      | @seq _ _ n _ _ _ _ first second =>
          have hfirst : ∀ q z, q ≤ n →
              Trace (compiled (SubexpSetupStorage.clearCmd p) port port) q
                (a.withPC (some (compiled (SubexpSetupStorage.clearCmd p) port port).entry)) z →
              ∀ j, (z.stacks j).length ≤ B := by
            cases first with
            | call prog ht =>
                apply StructuredSpace.call_stack_bound _ _ _ _
                  (compiled_site (SubexpSetupStorage.clearCmd p) port port) ht
                intro q z _ hz j
                exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
                  p 0 1 hz j).trans (hframe j)
          have hmiddle := hfirst _ _ le_rfl (compiled_trace first port port)
          exact StructuredSpace.sequence_stack_bound first second port port hfirst
            (ih second hmiddle) (compiled (SubexpSetupStorage.clearMany (p :: ps)) port port)
            (siteAddress (SubexpSetupStorage.clearMany (p :: ps)))
            (exitAddress (SubexpSetupStorage.clearMany (p :: ps)))
            (compiled_site (SubexpSetupStorage.clearMany (p :: ps)) port port)

private theorem clearMany_lift_prefix (ports : List (Fin 896))
    (inputStack outputStack : Fin 896) {steps B : ℕ} {a e : Data}
    (he : Eval (liftCommand (SubexpSetupStorage.clearMany ports) inputStack outputStack
      FactorEnvironment.registerMap id) steps a e)
    (hframe : ∀ j, (a.stacks j).length ≤ B) :
    ∀ q z, q ≤ steps → Trace (compiled (liftCommand (SubexpSetupStorage.clearMany ports) inputStack outputStack
      FactorEnvironment.registerMap id) 854 853) q
      (a.withPC (some (compiled (liftCommand (SubexpSetupStorage.clearMany ports) inputStack outputStack
      FactorEnvironment.registerMap id) 854 853).entry)) z →
      ∀ j, (z.stacks j).length ≤ B := by
  let inner := projectState FactorEnvironment.registerMap id a
  have hr : Function.Injective FactorEnvironment.registerMap := Fin.castAdd_injective _ _
  have hlocal := SubexpSetupStorage.clearMany_eval ports inner
  have ht := compiled_halt_trace hlocal inputStack outputStack
  have hspace := StructuredSpace.compiled_halt_stack_bound hlocal inputStack outputStack
    (by
      change ∀ q z, q ≤ SubexpSetupStorage.clearManyCost ports inner →
        Trace (compiled (SubexpSetupStorage.clearMany ports) inputStack inputStack) q
          (inner.withPC (some (compiled (SubexpSetupStorage.clearMany ports)
            inputStack inputStack).entry)) z → ∀ j, (z.stacks j).length ≤ B
      exact clearMany_prefix ports inputStack hlocal hframe)
  have hcall := eval_liftCommand_from_state (SubexpSetupStorage.clearMany ports) inputStack outputStack
    FactorEnvironment.registerMap id a hr Function.injective_id hlocal
  have htime := StreamResources.eval_steps_eq 854 853 he hcall
  subst steps
  have hglobal := StructuredSpace.liftProgram_stack_bound
    (compiled (SubexpSetupStorage.clearMany ports) inputStack outputStack) FactorEnvironment.registerMap id
    (a.withPC none) hr Function.injective_id ht hspace hframe
  have hinit : ProgramLinking.embedCfg FactorEnvironment.registerMap id id none (a.withPC none)
      (inner.withPC (some (compiled (SubexpSetupStorage.clearMany ports) inputStack outputStack).entry)) =
      a.withPC (some (ProgramLinking.liftProgram (compiled (SubexpSetupStorage.clearMany ports) inputStack outputStack)
        FactorEnvironment.registerMap id).entry) := by
    change (embedState FactorEnvironment.registerMap id a inner).withPC _ = _
    rw [embedState_project FactorEnvironment.registerMap id a hr Function.injective_id]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases hcall with
  | call prog htrace =>
      exact StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (liftCommand (SubexpSetupStorage.clearMany ports) inputStack outputStack
      FactorEnvironment.registerMap id) 854 853) htrace hglobal

/-- The paid arithmetic reset only clears cells; it preserves the same
per-stack envelope throughout its actual lifted execution. -/
theorem reset_prefix {steps B : ℕ} {a e : Data}
    (he : Eval FactorEnvironment.reset steps a e)
    (hframe : ∀ j, (a.stacks j).length ≤ B) :
    ∀ q z, q ≤ steps → Trace (compiled FactorEnvironment.reset 854 853) q
      (a.withPC (some (compiled FactorEnvironment.reset 854 853).entry)) z →
      ∀ j, (z.stacks j).length ≤ B :=
  clearMany_lift_prefix FactorEnvironment.environmentPorts 5 5 he hframe

/-- Array addition followed by reclamation preserves one caller envelope.
Only the independent physical cap of the28 arithmetic ports enters the budget. -/
theorem accumulate_prefix (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J P B steps : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a e : Data) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hp : projectState additionRegisters additionStacks a =
      Normalize.state (a.regs ∘ additionRegisters) M.bits width degree
        (Product.bytes seed) (Product.bytes source))
    (hinput : ∀ j, (a.stacks (additionStacks j)).length ≤ P)
    (hframe : ∀ j, (a.stacks j).length ≤ B)
    (hbudget : 28 * P + additionBudget n (baseWidth p t) d u J ≤ B)
    (he : Eval accumulate steps a e) :
    ∀ q z, q ≤ steps → Trace (compiled accumulate 854 853) q
      (a.withPC (some (compiled accumulate 854 853).entry)) z →
      ∀ j, (z.stacks j).length ≤ B := by
  cases he with
  | seq first second =>
      have hfirst := add_prefix p t M cache source seed hsource hseed a _ width degree
        hd hw hp hinput hframe hbudget first
      have hmiddle := hfirst _ _ le_rfl (compiled_trace first 854 853)
      exact StructuredSpace.sequence_stack_bound first second 854 853 hfirst
        (reset_prefix second hmiddle) (compiled accumulate 854 853)
        (siteAddress accumulate) (exitAddress accumulate) (compiled_site accumulate 854 853)


/-- Both binary controller words are physically reclaimed after the exhausted
loop, including the possible terminal overflow bit of the assignment cursor. -/
def finalize : Code := liftCommand (SubexpSetupStorage.clearMany [859, 860]) 859 853
  FactorEnvironment.registerMap id

noncomputable def finalized (a : Data) : Data :=
  embedState FactorEnvironment.registerMap id a
    (SubexpSetupStorage.clearManyState [859, 860]
      (projectState FactorEnvironment.registerMap id a))

theorem finalize_eval (a : Data) :
    Eval finalize (2 * (a.stacks 859).length + 2 * (a.stacks 860).length + 7)
      a (finalized a) := by
  have he := eval_liftCommand_from_state (SubexpSetupStorage.clearMany [859, 860]) 859 853
    FactorEnvironment.registerMap id a (Fin.castAdd_injective _ _) Function.injective_id
    (SubexpSetupStorage.clearMany_eval [859, 860]
      (projectState FactorEnvironment.registerMap id a))
  convert he using 1
  · rfl
  · simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, projectState]
    omega
  · rfl

theorem finalized_stacks (a : Data) :
    (finalized a).stacks = Function.update (Function.update a.stacks 859 []) 860 [] := by
  funext i
  rw [show (finalized a).stacks i =
      (SubexpSetupStorage.clearManyState [859, 860]
        (projectState FactorEnvironment.registerMap id a)).stacks i from
    embedState_stack FactorEnvironment.registerMap id a _ Function.injective_id i]
  simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState, projectState]

theorem finalize_prefix {steps B : ℕ} {a e : Data} (he : Eval finalize steps a e)
    (hframe : ∀ j, (a.stacks j).length ≤ B) :
    ∀ q z, q ≤ steps → Trace (compiled finalize 854 853) q
      (a.withPC (some (compiled finalize 854 853).entry)) z →
      ∀ j, (z.stacks j).length ≤ B :=
  clearMany_lift_prefix [859, 860] 859 853 he hframe

/-- The complete head-rescan control, including paid initialization and cleanup. -/
def scan (accepted : Code) : Code := .seq seed (.seq (command accepted) finalize)

def scanProgram (accepted : Code) := compiled (scan accepted) 651 853

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
