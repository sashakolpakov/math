import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDotControl
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatMul
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions
import OAI.Algorithms.SubexponentialSAT.SubexpFlatLift
import OAI.Algorithms.SubexponentialSAT.SubexpInputZip

namespace OAI.Algorithms

/-!
# Concrete residue-field dot products for beta construction

The finite control below uses the flat quartic multiplication and addition
machines. Arithmetic is performed with the prepared exponent-one modulus p.
The subsequent canonical lift to coefficient words is a separate stage.
-/

namespace SubexponentialSAT.SubexpInputBitProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpSymbolicCost SubexpSelectedConversions
open scoped BigOperators

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev ResidueCode (p : ℕ) := QuarticCode p 0

def dotProgram := SubexpDotControl.program
  SubexpQuarticFlatMul.program SubexpFlatAdd.program

private theorem mul_initial {B : ℕ} (m w : List Bool) (t a b : Quad (Word B)) :
    SubexpQuarticFlatMul.initialStore m w t a b =
      SubexpDotControl.mulStore m (SubexpQuarticFlatMul.flat t) w
        (SubexpQuarticFlatMul.flat a) (SubexpQuarticFlatMul.flat b) [] := by
  funext j
  by_cases h70 : j = 70
  · subst j; simp [SubexpQuarticFlatMul.initialStore,
      SubexpDotControl.mulStore]
  by_cases h71 : j = 71
  · subst j; simp [SubexpQuarticFlatMul.initialStore,
      SubexpDotControl.mulStore]
  by_cases hj : j.val < 61
  · have h66 : j.val ≠ 66 := by omega
    have h72 : j.val ≠ 72 := by omega
    have h73 : j.val ≠ 73 := by omega
    have h74 : j.val ≠ 74 := by omega
    simp [SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.bankStore,
      SubexpDotControl.mulStore, hj, h70, h71, Fin.ext_iff, h66, h72, h73, h74]
  · simp [SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.bankStore,
      SubexpDotControl.mulStore, hj, h70, h71]

private theorem mul_final {B : ℕ} (m w : List Bool) (t out : Quad (Word B)) :
    SubexpQuarticFlatMul.finalStore m w t out =
      SubexpDotControl.mulStore m (SubexpQuarticFlatMul.flat t) w [] []
        (SubexpQuarticFlatMul.flat out) := by
  funext j
  by_cases h70 : j = 70
  · subst j; simp [SubexpQuarticFlatMul.finalStore,
      SubexpQuarticFlatMul.bankStore, SubexpDotControl.mulStore]
  by_cases h71 : j = 71
  · subst j; simp [SubexpQuarticFlatMul.finalStore,
      SubexpQuarticFlatMul.bankStore, SubexpDotControl.mulStore]
  by_cases hj : j.val < 61
  · have h66 : j.val ≠ 66 := by omega
    have h72 : j.val ≠ 72 := by omega
    have h73 : j.val ≠ 73 := by omega
    have h74 : j.val ≠ 74 := by omega
    simp [SubexpQuarticFlatMul.finalStore, SubexpQuarticFlatMul.bankStore,
      SubexpDotControl.mulStore, hj, h70, h71, Fin.ext_iff, h66, h72, h73, h74]
  · simp [SubexpQuarticFlatMul.finalStore, SubexpQuarticFlatMul.bankStore,
      SubexpDotControl.mulStore, hj, h70, h71]

theorem flat_eq_add_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatMul.flat a = SubexpFlatAdd.encode a := by
  cases a
  simp [SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, SubexpFlatAdd.encode, SubexpFlatAdd.flatten,
    SubexpFlatAdd.quadWords, Quad.toFn]

private theorem add_ready (regs : Fin 8 → Bool) (m a b w : List Bool) :
    SubexpFlatAdd.ready regs m a b w [] (fun _ => []) =
      (⟨regs, SubexpDotControl.addStore m w a b⟩ : State 8 20) := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext j
    fin_cases j <;> simp [SubexpFlatAdd.ready, SubexpFlatAdd.state,
      SubexpFlatAdd.«stacks», SubexpDotControl.addStore, Fin.addCases,
      Fin.coe_ofNat_eq_mod]

variable {p : ℕ} [Fact p.Prime]

def multiply (source : Prepared p 0) (a b : ResidueCode p) : ResidueCode p :=
  (source.program.mulRun a b).1

def add (source : Prepared p 0) (a b : ResidueCode p) : ResidueCode p :=
  (source.program.addRun a b).1

theorem mul_contract (source : Prepared p 0) (width : List Bool)
    (hw : width.length = baseWidth p 1) :
    SubexpDotControl.MulContract SubexpQuarticFlatMul.program (baseWidth p 1)
      SubexpQuarticFlatMul.flat (multiply source) source.modulus.bits
      (SubexpQuarticFlatMul.flat source.reduction) width := by
  intro regs a b
  obtain ⟨rf, ht⟩ := SubexpQuarticFlatMul.program_run p 1 source.modulus
    source.reduction a b width hw regs
  rw [mul_initial, mul_final] at ht
  exact ⟨rf, ht⟩

theorem add_contract (source : Prepared p 0) (width : List Bool)
    (hw : width.length = baseWidth p 1) :
    SubexpDotControl.AddContract SubexpFlatAdd.program (baseWidth p 1)
      SubexpQuarticFlatMul.flat (add source) source.modulus.bits width := by
  intro regs a b
  obtain ⟨rf, ht⟩ := SubexpFlatAdd.program_runs_uniform p 1 source.modulus
    regs a b width (fun _ => []) hw
  rw [add_ready, add_ready] at ht
  simp only [← flat_eq_add_encode] at ht
  exact ⟨rf, ht⟩

theorem multiply_decode (source : Prepared p 0) (a b : ResidueCode p) :
    source.residueRing.decode (multiply source a b) =
      source.residueRing.decode a * source.residueRing.decode b :=
  source.residueRing.mul_correct a b

theorem add_decode (source : Prepared p 0) (a b : ResidueCode p) :
    source.residueRing.decode (add source a b) =
      source.residueRing.decode a + source.residueRing.decode b :=
  source.residueRing.add_correct a b

/-- Pure specifications of the exact words computed by the actual programs. -/
def dotOutput {D : ℕ} (source : Prepared p 0) (row x : Fin D → ResidueCode p) : ResidueCode p :=
  SubexpDotControl.foldPairs (multiply source) (add source) source.zero
    (SubexpDotControl.pairsFor row x)

def betaOutput {D : ℕ} (source : Prepared p 0) (row x : Fin D → ResidueCode p) : QuarticCode p D :=
  betaLift source D (dotOutput source row x)

/-- The output is computed by the actual finite quartic arithmetic programs at
modulus p, and its decoded value is the complete D-coordinate dot product. -/
theorem dot_execute_spec {D : ℕ} (source : Prepared p 0)
    (row x : Fin D → ResidueCode p) (width suffix : List Bool)
    (hw : width.length = baseWidth p 1) (d : SubexpDotControl.Data)
    (hd : d.stacks = SubexpDotControl.dotStore source.modulus.bits
      (SubexpQuarticFlatMul.flat source.reduction) width
      (SubexpQuarticFlatMul.flat source.zero)
      (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat
        (SubexpDotControl.pairsFor row x) ++ suffix) [] [] []) :
    ∃ (rf : Fin 8 → Bool) (result : ResidueCode p),
      RunsIn dotProgram (D * (SubexpDotControl.pairCost (baseWidth p 1) + 2) + 3)
        (d.withPC (some dotProgram.entry))
        ((SubexpDotControl.dataState rf source.modulus.bits
          (SubexpQuarticFlatMul.flat source.reduction) width
          (SubexpQuarticFlatMul.flat result) suffix [] [] []).withPC none) ∧
      source.residueRing.decode result =
        (SubexpInputCode.dotWithCost (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i))).1 ∧ result = dotOutput source row x := by
  obtain ⟨rf, ht⟩ := SubexpDotControl.program_execute
    SubexpQuarticFlatMul.program SubexpFlatAdd.program (baseWidth p 1)
    SubexpQuarticFlatMul.flat (multiply source) (add source)
    source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction) width
    (mul_contract source width hw) (add_contract source width hw)
    SubexpQuarticFlatMul.flat_length (SubexpDotControl.pairsFor row x) d source.zero suffix hd
  refine ⟨rf, SubexpDotControl.foldPairs (multiply source) (add source) source.zero
    (SubexpDotControl.pairsFor row x), ?_, ?_⟩
  · simpa only [dotProgram, SubexpDotControl.pairsFor_length] using ht
  · constructor
    · exact SubexpDotControl.foldPairs_dot source.residueRing.decode
        (multiply source) (add source) (multiply_decode source) (add_decode source)
        source.zero source.residueRing.zero_correct row x
    · rfl

theorem dot_execute {D : ℕ} (source : Prepared p 0)
    (row x : Fin D → ResidueCode p) (width suffix : List Bool)
    (hw : width.length = baseWidth p 1) (d : SubexpDotControl.Data)
    (hd : d.stacks = SubexpDotControl.dotStore source.modulus.bits
      (SubexpQuarticFlatMul.flat source.reduction) width
      (SubexpQuarticFlatMul.flat source.zero)
      (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat
        (SubexpDotControl.pairsFor row x) ++ suffix) [] [] []) :
    ∃ (rf : Fin 8 → Bool) (result : ResidueCode p),
      RunsIn dotProgram (D * (SubexpDotControl.pairCost (baseWidth p 1) + 2) + 3)
        (d.withPC (some dotProgram.entry))
        ((SubexpDotControl.dataState rf source.modulus.bits
          (SubexpQuarticFlatMul.flat source.reduction) width
          (SubexpQuarticFlatMul.flat result) suffix [] [] []).withPC none) ∧
      source.residueRing.decode result =
        (SubexpInputCode.dotWithCost (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i))).1 := by
  obtain ⟨rf, result, ht, hv, _⟩ := dot_execute_spec source row x width suffix hw d hd
  exact ⟨rf, result, ht, hv⟩

def widen (base : Fin 79 → List Bool) (targetWidth : List Bool) (j : Fin 80) : List Bool :=
  if h : j.val < 79 then base ⟨j.val, h⟩ else targetWidth

def betaState (regs : Fin 8 → Bool)
    (modulus reduction sourceWidth targetWidth acc source : List Bool) : State 8 80 :=
  ⟨regs, widen (SubexpDotControl.dotStore modulus reduction sourceWidth acc source [] [] []) targetWidth⟩

def dotPorts : Fin 79 → Fin 80 := Fin.castAdd 1

omit [Fact p.Prime] in
theorem dotPorts_injective : Function.Injective dotPorts := Fin.castAdd_injective _ _

def liftPorts (j : Fin 20) : Fin 80 :=
  if j = 5 then 66 else if j = 8 then 77 else if j = 10 then 74
  else if j = 11 then 79 else ⟨j.val, by omega⟩

omit [Fact p.Prime] in
theorem liftPorts_injective : Function.Injective liftPorts := by decide

abbrev betaCommand : Cmd 8 80 :=
  .seq (.call (ProgramLinking.liftProgram dotProgram id dotPorts))
    (.call (ProgramLinking.liftProgram SubexpFlatLift.program id liftPorts))

abbrev betaProgram : Program 8 80 (size betaCommand + 1) := compiled betaCommand 78 77

omit [Fact p.Prime] in
theorem flat_eq_lift_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatMul.flat a = SubexpFlatLift.encode a := by
  cases a
  simp [SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, SubexpFlatLift.encode, SubexpFlatLift.flatten,
    SubexpFlatLift.quadWords, Quad.toFn]

omit [Fact p.Prime] in
private theorem embed_dot (regs frameRegs : Fin 8 → Bool)
    (m t sw tw acc source oldAcc oldSource : List Bool) :
    embedState id dotPorts (betaState frameRegs m t sw tw oldAcc oldSource)
      (SubexpDotControl.dataState regs m t sw acc source [] [] []) =
      betaState regs m t sw tw acc source := by
  apply SubexpScanPrimitives.embedState_eq id dotPorts Function.injective_id dotPorts_injective
  · intro i; rfl
  · intro i
    simp [betaState, widen, dotPorts, SubexpDotControl.dataState, i.isLt]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h : ¬ j.val < 79 := by
      intro h
      exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [betaState, widen, h]

omit [Fact p.Prime] in
private theorem embed_lift (regs frameRegs : Fin 8 → Bool)
    (m t sw tw acc source oldAcc : List Bool) :
    embedState id liftPorts (betaState frameRegs m t sw tw oldAcc source)
      (SubexpFlatLift.ready regs m acc [] sw tw (fun _ => [])) =
      betaState regs m t sw tw acc source := by
  apply SubexpScanPrimitives.embedState_eq id liftPorts Function.injective_id liftPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h77 : j.val ≠ 77 := by
      intro he
      exact hj ⟨8, Fin.ext he.symm⟩
    by_cases h : j.val < 79
    · simp [betaState, widen, h, SubexpDotControl.dotStore, Fin.ext_iff, h77]
    · simp [betaState, widen, h]

/-- The complete finite beta program computes a residue-field dot product,
then executes canonical coefficient lifting. The two moduli are never
identified: source arithmetic uses p, while the target decoder uses p^(D+1). -/
theorem beta_execute_spec {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth suffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (result : QuarticCode p D),
      RunsIn betaProgram
        (D * (SubexpDotControl.pairCost (baseWidth p 1) + 2) + 3 +
          2100 * (baseWidth p 1 + baseWidth p (D + 1) + 2)^2 + 1)
        ((betaState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero)
          (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat
            (SubexpDotControl.pairsFor row x) ++ suffix)).withPC (some betaProgram.entry))
        ((betaState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat result) suffix).withPC none) ∧
      target.ring.decode result =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) ∧ result = betaOutput source row x := by
  let d0 := SubexpDotControl.dataState regs source.modulus.bits
    (SubexpQuarticFlatMul.flat source.reduction) sourceWidth
    (SubexpQuarticFlatMul.flat source.zero)
    (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat
      (SubexpDotControl.pairsFor row x) ++ suffix) [] [] []
  obtain ⟨rd, residue, ⟨nd, hnd, hdot⟩, hvalue, hresult⟩ := dot_execute_spec source row x sourceWidth suffix hs d0 rfl
  have hd := eval_call_lifted dotProgram id dotPorts
    (betaState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
      sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero)
      (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat
        (SubexpDotControl.pairsFor row x) ++ suffix))
    Function.injective_id dotPorts_injective
    (a := d0)
    (b := SubexpDotControl.dataState rd source.modulus.bits
      (SubexpQuarticFlatMul.flat source.reduction) sourceWidth
      (SubexpQuarticFlatMul.flat residue) suffix [] [] []) hdot
  change Eval _ _ (embedState _ _ _ (SubexpDotControl.dataState _ _ _ _ _ _ _ _ _)) _ at hd
  rw [embed_dot, embed_dot] at hd
  obtain ⟨rf, nl, hnl, hlift⟩ := SubexpFlatLift.program_runs p (D + 1) source.modulus
    (Nat.succ_pos D) rd residue sourceWidth targetWidth (fun _ => []) hs hT
  have hl := eval_call_lifted SubexpFlatLift.program id liftPorts
    (betaState rd source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
      sourceWidth targetWidth (SubexpQuarticFlatMul.flat residue) suffix)
    Function.injective_id liftPorts_injective
    (a := SubexpFlatLift.ready rd source.modulus.bits (SubexpFlatLift.encode residue) []
      sourceWidth targetWidth (fun _ => []))
    (b := SubexpFlatLift.ready rf source.modulus.bits
      (SubexpFlatLift.encode (SubexpWordLift.liftQuadRun p (D + 1) source.modulus residue).1) []
      sourceWidth targetWidth (fun _ => [])) hlift
  rw [embed_lift, embed_lift] at hl
  simp only [← flat_eq_lift_encode] at hl
  refine ⟨rf, (SubexpWordLift.liftQuadRun p (D + 1) source.modulus residue).1,
    ⟨nd + nl + 1, by omega, compiled_halt_trace (Eval.seq hd hl) 78 77⟩, ?_⟩
  constructor
  · change target.ring.decode (betaLift source D residue) = _
    rw [betaLift_decode source target, hvalue]
    rfl
  · change betaLift source D residue = betaLift source D (dotOutput source row x)
    rw [hresult]

theorem beta_execute {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth suffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (result : QuarticCode p D),
      RunsIn betaProgram
        (D * (SubexpDotControl.pairCost (baseWidth p 1) + 2) + 3 +
          2100 * (baseWidth p 1 + baseWidth p (D + 1) + 2)^2 + 1)
        ((betaState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero)
          (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat
            (SubexpDotControl.pairsFor row x) ++ suffix)).withPC (some betaProgram.entry))
        ((betaState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat result) suffix).withPC none) ∧
      target.ring.decode result =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) := by
  obtain ⟨rf, result, ht, hv, _⟩ :=
    beta_execute_spec source target row x sourceWidth targetWidth suffix hs hT regs
  exact ⟨rf, result, ht, hv⟩

/-- Primitive-machine beta evaluation, retaining the complete output encoding
and both source and target width parameters in the explicit bound. -/
theorem beta_primitive {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth suffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (result : QuarticCode p D),
      SubexpQuarticFlatMul.PrimitiveRunsIn betaProgram
        (primitiveOverhead betaProgram *
          (D * (SubexpDotControl.pairCost (baseWidth p 1) + 2) + 3 +
            2100 * (baseWidth p 1 + baseWidth p (D + 1) + 2)^2 + 1))
        ((betaState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
            sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero)
            (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat
              (SubexpDotControl.pairsFor row x) ++ suffix)).withPC (some betaProgram.entry))
        ((betaState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
            sourceWidth targetWidth (SubexpQuarticFlatMul.flat result) suffix).withPC none) ∧
      target.ring.decode result =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) := by
  obtain ⟨rf, result, ht, hv⟩ := beta_execute source target row x sourceWidth targetWidth suffix hs hT regs
  exact ⟨rf, result, SubexpQuarticFlatMul.primitiveRunsIn_of_runsIn _ ht, hv⟩

def sourceState (regs : Fin 8 → Bool)
    (modulus reduction sourceWidth targetWidth acc pairs row input : List Bool) : State 8 82 :=
  ⟨regs, fun j => if h : j.val < 80 then
    (betaState regs modulus reduction sourceWidth targetWidth acc pairs).stacks ⟨j.val, h⟩
    else if j.val = 80 then row else input⟩

def sourceZipPorts : Fin 8 → Fin 82 := ![80, 81, 70, 71, 72, 75, 78, 76]
def sourceBetaPorts : Fin 80 → Fin 82 := Fin.castAdd 2

omit [Fact p.Prime] in
theorem sourceZipPorts_injective : Function.Injective sourceZipPorts := by decide

omit [Fact p.Prime] in
theorem sourceBetaPorts_injective : Function.Injective sourceBetaPorts := Fin.castAdd_injective _ _

omit [Fact p.Prime] in
private theorem embed_source_zip (regs frameRegs : Fin 8 → Bool)
    (m t sw tw acc pairs row input oldPairs oldRow oldInput : List Bool) :
    embedState id sourceZipPorts
      (sourceState frameRegs m t sw tw acc oldPairs oldRow oldInput)
      (SubexpInputZip.ready regs row input [] pairs) =
      sourceState regs m t sw tw acc pairs row input := by
  apply SubexpScanPrimitives.embedState_eq id sourceZipPorts
    Function.injective_id sourceZipPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h80 : j.val ≠ 80 := fun h => hj ⟨0, Fin.ext h.symm⟩
    have h81 : j.val ≠ 81 := fun h => hj ⟨1, Fin.ext h.symm⟩
    have h78 : j.val ≠ 78 := fun h => hj ⟨6, Fin.ext h.symm⟩
    have hlt : j.val < 80 := by omega
    by_cases h79 : j.val < 79
    · simp [sourceState, hlt, betaState, widen, h79, SubexpDotControl.dotStore,
        Fin.ext_iff, h78]
    · simp [sourceState, hlt, betaState, widen, h79]

omit [Fact p.Prime] in
private theorem embed_source_beta (regs frameRegs : Fin 8 → Bool)
    (m t sw tw acc pairs row input oldAcc oldPairs : List Bool) :
    embedState id sourceBetaPorts
      (sourceState frameRegs m t sw tw oldAcc oldPairs row input)
      (betaState regs m t sw tw acc pairs) =
      sourceState regs m t sw tw acc pairs row input := by
  apply SubexpScanPrimitives.embedState_eq id sourceBetaPorts
    Function.injective_id sourceBetaPorts_injective
  · intro i; rfl
  · intro i; simp [sourceState, sourceBetaPorts, i.isLt]
  · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h : ¬ j.val < 80 := by
      intro h
      exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [sourceState, h]

abbrev sourceCommand : Cmd 8 82 :=
  .seq (.call (ProgramLinking.liftProgram SubexpInputZip.program id sourceZipPorts))
    (.call (ProgramLinking.liftProgram betaProgram id sourceBetaPorts))

abbrev sourceProgram : Program 8 82 (size sourceCommand + 1) := compiled sourceCommand 80 77

def sourceSteps (D p : ℕ) : ℕ :=
  D * (52 * (4 * baseWidth p 1) + 53) + 12 +
    (D * (SubexpDotControl.pairCost (baseWidth p 1) + 2) + 3 +
      2100 * (baseWidth p 1 + baseWidth p (D + 1) + 2)^2 + 1) + 1

omit [Fact p.Prime] in
theorem sourceSteps_polynomial (D p : ℕ) :
    sourceSteps D p ≤ 430000 * (D + 2)^2 * (Nat.log 2 p + 3)^2 := by
  simpa only [sourceSteps, baseWidth, Nat.one_mul, Nat.add_assoc] using
    SubexpInputZip.sourceBound_polynomial D (Nat.log 2 p + 1)

/-- Complete beta construction from separate row and coordinate streams. The
finite program physically pairs those streams, performs all arithmetic in
the residue field, and executes the canonical lift to coefficient words. -/
theorem source_execute_spec {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth : List Bool)
    (rowSuffix inputSuffix pairSuffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (result : QuarticCode p D),
      RunsIn sourceProgram (sourceSteps D p)
        ((sourceState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero) pairSuffix
          (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map row) ++ rowSuffix)
          (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map x) ++ inputSuffix)).withPC
            (some sourceProgram.entry))
        ((sourceState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat result) pairSuffix rowSuffix inputSuffix).withPC none) ∧
      target.ring.decode result =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) ∧ result = betaOutput source row x := by
  obtain ⟨rz, hz⟩ := SubexpInputZip.program_rows_trace SubexpQuarticFlatMul.flat
    SubexpQuarticFlatMul.flat_length row x regs rowSuffix inputSuffix pairSuffix
  let initialState := sourceState regs source.modulus.bits
    (SubexpQuarticFlatMul.flat source.reduction) sourceWidth targetWidth
    (SubexpQuarticFlatMul.flat source.zero) pairSuffix
    (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map row) ++ rowSuffix)
    (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map x) ++ inputSuffix)
  have hez := eval_call_lifted SubexpInputZip.program id sourceZipPorts initialState
    Function.injective_id sourceZipPorts_injective hz
  change Eval _ _ (embedState _ _ (sourceState _ _ _ _ _ _ _ _ _) _)
    (embedState _ _ (sourceState _ _ _ _ _ _ _ _ _) _) at hez
  rw [embed_source_zip, embed_source_zip] at hez
  simp only [Nat.zero_add] at hez
  obtain ⟨rf, result, ⟨nb, hnb, hb⟩, hv, heq⟩ :=
    beta_execute_spec source target row x sourceWidth targetWidth pairSuffix hs hT rz
  let middleState := sourceState rz source.modulus.bits
    (SubexpQuarticFlatMul.flat source.reduction) sourceWidth targetWidth
    (SubexpQuarticFlatMul.flat source.zero)
    (SubexpDotControl.encodePairs SubexpQuarticFlatMul.flat (SubexpDotControl.pairsFor row x) ++ pairSuffix)
    rowSuffix inputSuffix
  have heb := eval_call_lifted betaProgram id sourceBetaPorts middleState
    Function.injective_id sourceBetaPorts_injective hb
  change Eval _ _ (embedState _ _ (sourceState _ _ _ _ _ _ _ _ _) _)
    (embedState _ _ (sourceState _ _ _ _ _ _ _ _ _) _) at heb
  rw [embed_source_beta, embed_source_beta] at heb
  exact ⟨rf, result, ⟨_, by unfold sourceSteps; omega,
    compiled_halt_trace (Eval.seq hez heb) 80 77⟩, hv, heq⟩

theorem source_execute {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth : List Bool)
    (rowSuffix inputSuffix pairSuffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (result : QuarticCode p D),
      RunsIn sourceProgram (sourceSteps D p)
        ((sourceState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero) pairSuffix
          (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map row) ++ rowSuffix)
          (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map x) ++ inputSuffix)).withPC
            (some sourceProgram.entry))
        ((sourceState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat result) pairSuffix rowSuffix inputSuffix).withPC none) ∧
      target.ring.decode result =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) := by
  obtain ⟨rf, result, ht, hv, _⟩ :=
    source_execute_spec source target row x sourceWidth targetWidth rowSuffix inputSuffix pairSuffix hs hT regs
  exact ⟨rf, result, ht, hv⟩

theorem source_execute_exact {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth : List Bool)
    (rowSuffix inputSuffix pairSuffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ rf : Fin 8 → Bool,
      RunsIn sourceProgram (sourceSteps D p)
        ((sourceState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero) pairSuffix
          (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map row) ++ rowSuffix)
          (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map x) ++ inputSuffix)).withPC
            (some sourceProgram.entry))
        ((sourceState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
          sourceWidth targetWidth (SubexpQuarticFlatMul.flat (betaOutput source row x)) pairSuffix rowSuffix inputSuffix).withPC none) ∧
      target.ring.decode (betaOutput source row x) =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) := by
  obtain ⟨rf, result, ht, hv, heq⟩ :=
    source_execute_spec source target row x sourceWidth targetWidth rowSuffix inputSuffix pairSuffix hs hT regs
  subst result
  exact ⟨rf, ht, hv⟩

theorem source_primitive {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth : List Bool)
    (rowSuffix inputSuffix pairSuffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (result : QuarticCode p D),
      SubexpQuarticFlatMul.PrimitiveRunsIn sourceProgram
        (primitiveOverhead sourceProgram * sourceSteps D p)
        ((sourceState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
            sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero) pairSuffix
            (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map row) ++ rowSuffix)
            (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map x) ++ inputSuffix)).withPC
              (some sourceProgram.entry))
        ((sourceState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
            sourceWidth targetWidth (SubexpQuarticFlatMul.flat result) pairSuffix rowSuffix inputSuffix).withPC none) ∧
      target.ring.decode result =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) := by
  obtain ⟨rf, result, ht, hv⟩ :=
    source_execute source target row x sourceWidth targetWidth rowSuffix inputSuffix pairSuffix hs hT regs
  exact ⟨rf, result, SubexpQuarticFlatMul.primitiveRunsIn_of_runsIn _ ht, hv⟩

theorem source_exact_primitive {D : ℕ} (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (sourceWidth targetWidth : List Bool)
    (rowSuffix inputSuffix pairSuffix : List Bool)
    (hs : sourceWidth.length = baseWidth p 1)
    (hT : targetWidth.length = baseWidth p (D + 1)) (regs : Fin 8 → Bool) :
    ∃ rf : Fin 8 → Bool,
      SubexpQuarticFlatMul.PrimitiveRunsIn sourceProgram
        (primitiveOverhead sourceProgram * sourceSteps D p)
        ((sourceState regs source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
            sourceWidth targetWidth (SubexpQuarticFlatMul.flat source.zero) pairSuffix
            (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map row) ++ rowSuffix)
            (Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map x) ++ inputSuffix)).withPC
              (some sourceProgram.entry))
        ((sourceState rf source.modulus.bits (SubexpQuarticFlatMul.flat source.reduction)
            sourceWidth targetWidth (SubexpQuarticFlatMul.flat (betaOutput source row x)) pairSuffix rowSuffix inputSuffix).withPC none) ∧
      target.ring.decode (betaOutput source row x) =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) := by
  obtain ⟨rf, ht, hv⟩ :=
    source_execute_exact source target row x sourceWidth targetWidth rowSuffix inputSuffix pairSuffix hs hT regs
  exact ⟨rf, SubexpQuarticFlatMul.primitiveRunsIn_of_runsIn _ ht, hv⟩

end SubexponentialSAT.SubexpInputBitProgram

end OAI.Algorithms
