import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRTFrames
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRTInput
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterSelected

namespace OAI.Algorithms

/-!
# Actual selected-ring CRT execution in the Main allocation

The physical node and jet arrays enter the concrete preparation/controller/
cleanup program. The selected-ring execution theorem supplies the controller
trace and its computed value. The conclusion is the exact singleton buffer
and initialized decoder state required by the already verified finalizer.
-/

namespace SubexponentialSAT.SubexpMainCRTSelected

open BitProgram StructuredCalls SubexpMainProgram SubexpLiftRing SubexpQuarticRing

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) S.toPattern c)

local notation "D" => Fintype.card V
local notation "B" => baseWidth p (D + 1)
local notation "coeffs" => QuarticSearch.liftedCoefficients p (D + 1)

def runtimeBound {er es : ℕ} (alloc : SubexpMainCRT.Allocation es)
    (a : MainState er es) (Q : ℕ) (exponent : List Bool) : ℕ :=
  SubexpMainCRT.preparationBound alloc a +
    SubexpCRTOuterExecution.commandBudget p D Q exponent +
    2 * SubexpMainCRT.scratchBits alloc a + 19

omit [DecidableEq F] in
/-- Every premise is either an existing-word identity or a denotation of an
actual node/jet input. There is no assumed CRT trace or desired output value. -/
theorem execution {er es : ℕ} (alloc : SubexpMainCRT.Allocation es)
    (a : MainState er es) (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t one : SubexpCRTSelectedInput.Coefficient p D)
    (minusOne : Word B) (width exponent : List Bool)
    (nodes : Fin c.Q → SubexpCRTSelectedInput.Coefficient p D)
    (jets : Fin c.Q → SubexpCRTSelectedInput.Jet p D)
    (hD : 0 < D) (hw : width.length = B)
    (ht : t.map (wordValue p (D + 1)) = reductionData coeffs)
    (ho : SubexpCRTSelectedInput.decode p D one = 1)
    (hm : wordValue p (D + 1) minusOne = -1)
    (he : BinaryArithmetic.toNat exponent = p^4 - 2)
    (hn : ∀ i, SubexpCRTSelectedInput.decode p D (nodes i) =
      SubexpCRTAtZero.selectedNode S L i)
    (hj : ∀ i, SubexpCRTSelectedInput.denote p D (jets i) =
      SubexpCRTSelectedInput.selectedJet S L i)
    (hMword : a.stacks (persistent es 12) = M.bits)
    (hWword : a.stacks (persistent es 13) = width)
    (hTword : a.stacks (persistent es 14) = SubexpFlatAdd.encode t)
    (hEword : a.stacks (persistent es 29) = exponent)
    (hOword : a.stacks (persistent es 30) = SubexpFlatAdd.encode one)
    (hNword : a.stacks (persistent es 31) = minusOne.val)
    (hDword : CounterPrograms.value (a.stacks (persistent es 19)) = D)
    (hnodes : a.stacks (SubexpMainCRT.ordinary alloc 256) =
      (List.finRange c.Q).flatMap (fun i => SubexpFlatAdd.encode (nodes i)))
    (hjets : a.stacks (SubexpMainCRT.ordinary alloc 265) =
      (List.finRange c.Q).flatMap
        (fun i => SubexpPolynomialPowerProgram.encode p (D + 1) (jets i))) :
    ∃ n ≤ runtimeBound (p := p) (V := V) alloc a c.Q exponent, ∃ b : MainState er es,
      ∃ output : SubexpFlatCount.Code B,
      Eval (SubexpMainCRT.procedure er alloc).invoke n a b ∧
      SubexpHornerMachine.decode p (D + 1) coeffs output =
        SubexpCRTAtZero.selectedValue S L ∧
      b.stacks (persistent es 10) = SubexpFlatCount.flatPolynomial [output] ∧
      (SubexpMainDecode.procedure er es).project b = SubexpFlatCount.start
        ((SubexpMainDecode.procedure er es).project b).regs M.bits width
        (SubexpFlatCount.flatPolynomial [output]) ∧
      (∀ i : Fin 32, i ≠ 10 → b.stacks (persistent es i) = a.stacks (persistent es i)) ∧
      (∀ i : Fin (totalStacks es), alloc.ordinaryCount ≤ i.val → i.val < workStacks es →
        b.stacks i = a.stacks i) ∧
      (∀ i : Fin (totalStacks es), 7 ≤ i.val → i.val < 256 →
        b.stacks i = a.stacks i) := by
  obtain ⟨out, output, ⟨ncrt, hncrt, hcrt⟩, hout, hvalue⟩ :=
    SubexpCRTOuterSelected.program_value S L M t one minusOne width exponent nodes jets
      hD hw ht ho hm he hn hj (fun _ => false)
  have hinput := SubexpMainCRTInput.prepared_eq_outerInput alloc a p D M t one minusOne
    width exponent nodes jets hMword hWword hTword hEword hOword hNword hDword hnodes hjets
  have hrun : Computation.Trace (BitProgram.step SubexpCRTOuterProgram.program) ncrt
      (((SubexpMainCRT.crt er alloc).project (SubexpMainCRT.preparedData alloc a)).withPC
        (some SubexpCRTOuterProgram.program.entry)) (out.withPC none) := by
    rw [SubexpMainCRT.crt_project, hinput]
    exact hcrt
  obtain ⟨n, hcall, hbound⟩ := SubexpMainCRT.execution_bound alloc a out hrun
  let b := SubexpMainCRT.finalData alloc
    ((SubexpMainCRT.crt er alloc).install (SubexpMainCRT.preparedData alloc a) out)
  have hb : b.stacks (persistent es 10) = SubexpFlatCount.flatPolynomial [output] :=
    (SubexpMainCRT.phase_output alloc a out).trans
      (hout.trans (SubexpCRTOuterSelected.encode_singleton output))
  have hmodulus : b.stacks (persistent es 12) = M.bits :=
    (SubexpMainCRT.phase_input alloc a out 0).trans hMword
  have hwidth : b.stacks (persistent es 13) = width :=
    (SubexpMainCRT.phase_input alloc a out 1).trans hWword
  have hready := SubexpMainCRT.decoder_ready alloc
    ((SubexpMainCRT.crt er alloc).install (SubexpMainCRT.preparedData alloc a) out)
  change (SubexpMainDecode.procedure er es).project b = SubexpFlatCount.start
    ((SubexpMainDecode.procedure er es).project b).regs
    (b.stacks (persistent es 12)) (b.stacks (persistent es 13))
    (b.stacks (persistent es 10)) at hready
  rw [hmodulus, hwidth, hb] at hready
  refine ⟨n, ?_, b, output, hcall, hvalue, hb, hready, ?_, ?_, ?_⟩
  · unfold runtimeBound
    omega
  · intro i hi
    exact SubexpMainCRT.phase_persistent_frame alloc a out i hi
  · intro i hlo hhi
    exact SubexpMainCRT.phase_threshold_frame alloc a out i hlo hhi
  · intro i hlo hhi
    exact SubexpMainCRT.phase_low_frame alloc a out i hlo hhi

end SubexponentialSAT.SubexpMainCRTSelected

end OAI.Algorithms
