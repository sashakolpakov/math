import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixBridge
import OAI.Algorithms.SubexponentialSAT.SubexpRowLiftProgram
import OAI.Algorithms.SubexponentialSAT.SubexpRowLiftSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpRowSourceSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpRowCost

namespace OAI.Algorithms

/-! A fixed program from one source-field row expression to the complete
lifted coefficient array expected by the Taylor-row routine. Source code is
on 26; the fully reversed target row is returned on 87. -/

namespace SubexponentialSAT.SubexpRowToTaylor

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexpRowPostfixBridge (addValue mulValue loadValue addBound mulBound loadBound)

def program := ProgramLinking.link SubexpRowPostfixBridge.program SubexpRowLiftProgram.program

def runtimeBound (R b B sourceLength : ℕ) : ℕ :=
  SubexpRowCost.scale (R + 1) b * sourceLength +
    9 * ((R + 1) * (4 * b)) + 25 + 3000 * (R + 2) * (b + B + 2)^2

private theorem lift_layout (s : SubexpConvolutionControl.Store)
    (bits modulus sw tw : List Bool) (frame : Fin 6 → List Bool)
    (hlow : ∀ i : Fin 20, s (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) modulus [] [] sw [] frame).stacks i)
    (h74 : s 74 = tw) (h87 : s 87 = []) :
    ∀ i, SubexpRowLiftProgram.extracted s bits (SubexpRowLiftProgram.liftPorts i) =
      (SubexpFlatLift.ready (fun _ => false) modulus bits [] sw tw frame).stacks i := by
  intro i
  have h := hlow i
  fin_cases i <;> first
    | rfl
    | simp_all [SubexpRowLiftProgram.extracted, SubexpRowLiftProgram.liftPorts,
        SubexpPolynomialAddService.ports, DensePolynomialLoop.ready,
        DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
        SubexpFlatLift.ready, SubexpFlatLift.state, SubexpFlatLift.stackArray,
        Fin.addCases, Fin.coe_ofNat_eq_mod]

private theorem clean_output {l : ℕ} (context : Fin 252 → List Bool)
    (operands bits output : List Bool) (h21 : contextStore context 21 = []) :
    Function.update (Function.update
      (SubexpRowLiftProgram.extracted
        (physicalCfg (l := l) none false false false [] [true] operands context).stacks bits)
      21 []) 87 output = Function.update (contextStore context) 87 output := by
  let s := (physicalCfg (l := l) none false false false [] [true] operands context).stacks
  have hc26 : contextStore context 26 = [] := SubexpRowPostfixInterpreter.physicalCfg_code _ _ _ _ _ _ _ _
  have hc27 : contextStore context 27 = [] := SubexpRowPostfixInterpreter.physicalCfg_operands _ _ _ _ _ _ _ _
  have hc28 : contextStore context 28 = [] := SubexpRowPostfixInterpreter.physicalCfg_depth _ _ _ _ _ _ _ _
  have hs26 : s 26 = [] := SubexpRowPostfixInterpreter.physicalCfg_code _ _ _ _ _ _ _ _
  funext i
  by_cases h87 : i = 87
  · subst i; simp
  by_cases hi21 : i = 21
  · subst i; simp [SubexpRowLiftProgram.extracted, h21]
  by_cases h27 : i = 27
  · subst i; simp [SubexpRowLiftProgram.extracted, hc27]
  by_cases h28 : i = 28
  · subst i; simp [SubexpRowLiftProgram.extracted, hc28]
  by_cases h26 : i = 26
  · subst i; simp [SubexpRowLiftProgram.extracted, hc26] at hs26 ⊢
  simp only [Function.update_apply, h87, hi21, h27, h28, ite_false,
    SubexpRowLiftProgram.extracted]
  exact SubexpRowPostfixInterpreter.physicalCfg_frame _ _ _ _ _ _ _ _ _ h26 h28 h27

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0) (R : ℕ)
variable (sw tw : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)

/-- Concrete single-row execution. All arithmetic tables, parsing, copying,
and coefficient lifting occur inside this one fixed finite program. -/
theorem run (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) :
    letI : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
    letI : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
      ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
    let P := (e.map (loadValue source.zero (R + 1))).eval
    ∃ rf, RunsIn program
      (SubexpProjectedInterpreter.exprCost SubexpRowPolynomialCalls.encode
        (addBound p 1 source.program)
        (mulBound p 1 source.modulus source.reduction source.zero (R + 1))
        (loadValue source.zero (R + 1)) (loadBound p 1 (R + 1)) e + 5 +
        (9 * (SubexpCoefficientLiftArray.encodeArray P).length + 20 +
          3000 * (P.length + 1) * (baseWidth p 1 + baseWidth p μ + 2)^2))
      (physicalCfg (some program.entry) false false false
        (SubexpPostfixControl.serializeCode SubexpRowPolynomialCalls.encode e.compile) [] [] context)
      ((⟨rf, Function.update (contextStore context) 87
        (SubexpCoefficientLiftArray.encodeArray
          (SubexpCoefficientLiftArray.liftedArray p μ source.modulus P)).reverse⟩ :
        State 16 256).withPC none) := by
  let _ : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
  let _ : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
    ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  let P := (e.map (loadValue source.zero (R + 1))).eval
  let operands := Encoding.encodeList SubexpRowPolynomialCalls.encode [P]
  let middle := physicalCfg (l := 1) none false false false [] [true] operands context
  let s := middle.stacks
  have hs := SubexpRowPostfixBridge.run p 1 source.modulus source.reduction source.zero
    (R + 1) source.program sw frame context H (fun _ _ => rfl) hz e
  have hsframe (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = contextStore context i :=
    SubexpRowPostfixInterpreter.physicalCfg_frame (l := 1) none false false false
      [] [true] operands context i h26 h28 h27
  have hlow : ∀ i : Fin 20, s (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) source.modulus.bits [] [] sw [] frame).stacks i := by
    intro i
    rw [hsframe]
    · exact H.addStore i
    all_goals
      intro h
      have hv := congrArg Fin.val h
      change i.val = _ at hv
      have hi := i.isLt
      omega
  have h74' : s 74 = tw :=
    (hsframe 74 (by decide) (by decide) (by decide)).trans h74
  have h87' : s 87 = [] :=
    (hsframe 87 (by decide) (by decide) (by decide)).trans h87
  have h21' : s 21 = [] :=
    (hsframe 21 (by decide) (by decide) (by decide)).trans H.empty21
  obtain ⟨rf, hl⟩ := SubexpRowLiftProgram.program_run p μ source.modulus hμ s
    (fun _ => false) P sw tw frame H.widthLength hB rfl rfl h21'
    (SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (lift_layout s (SubexpCoefficientLiftArray.encodeArray P) source.modulus.bits sw tw frame hlow h74' h87')
  have hclean := clean_output (l := 1) context operands (SubexpCoefficientLiftArray.encodeArray P)
    (SubexpCoefficientLiftArray.encodeArray
      (SubexpCoefficientLiftArray.liftedArray p μ source.modulus P)).reverse H.empty21
  rw [hclean] at hl
  have hj := ProgramLinking.link_runsIn SubexpRowPostfixBridge.program
    SubexpRowLiftProgram.program hs rfl (by
      convert hl using 1
      simp [ProgramLinking.enter, StructuredProgram.State.withPC,
        SubexpRowPostfixInterpreter.physicalCfg_false_regs, s, middle, operands, P,
        SubexpPostfixControl.operandDepth]
      rfl)
  refine ⟨rf, ?_⟩
  simpa only [program, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    StructuredProgram.State.withPC, P, operands, s, middle,
    SubexpRowPostfixInterpreter.physicalCfg, SubexpPostfixGlobal.reindexCfg,
    SubexpPostfixInterpreter.cfg] using hj

theorem run_bounded (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) :
    letI : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
    letI : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
      ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
    let P := (e.map (loadValue source.zero (R + 1))).eval
    ∃ rf, RunsIn program
      (runtimeBound R (baseWidth p 1) (baseWidth p μ)
        (SubexpPostfixControl.serializeCode SubexpRowPolynomialCalls.encode e.compile).length)
      (physicalCfg (some program.entry) false false false
        (SubexpPostfixControl.serializeCode SubexpRowPolynomialCalls.encode e.compile) [] [] context)
      ((⟨rf, Function.update (contextStore context) 87
        (SubexpCoefficientLiftArray.encodeArray
          (SubexpCoefficientLiftArray.liftedArray p μ source.modulus P)).reverse⟩ :
        State 16 256).withPC none) := by
  let _ : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
  let _ : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
    ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  let P := (e.map (loadValue source.zero (R + 1))).eval
  obtain ⟨rf, n, hn, ht⟩ := run p μ source R sw tw frame context hμ H hz h74 h87 hB e
  refine ⟨rf, n, hn.trans ?_, ht⟩
  have hlen : P.length = R + 1 :=
    (SubexpRowPostfixBridge.validity p 1 source.modulus source.reduction source.zero
      (R + 1) source.program).eval_valid e
  have hbits : (SubexpCoefficientLiftArray.encodeArray P).length = (R + 1) * (4 * baseWidth p 1) := by
    change (SubexpRowPolynomialCalls.encode P).length = _
    rw [SubexpRowCost.encode_length, hlen]
  have hc := (SubexpRowCost.expressionCost_le p 1 source.modulus source.reduction source.zero
    (R + 1) source.program e).trans (Nat.mul_le_mul_left _
      (SubexpRowCost.work_le_source SubexpRowPolynomialCalls.encode e))
  change _ ≤ runtimeBound R (baseWidth p 1) (baseWidth p μ) _
  rw [hbits, hlen]
  unfold runtimeBound
  rw [show R + 1 + 1 = R + 2 by omega]
  omega

/-- The same fixed row program executes on the primitive machine, with only
the compiler's input-independent multiplicative overhead. -/
theorem primitive_run (hμ : 0 < μ)
    (H : SubexpRowPostfixContext.Ready p 1 source.modulus source.reduction source.zero
      (R + 1) sw frame context)
    (hz : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false)
    (h74 : contextStore context 74 = tw) (h87 : contextStore context 87 = [])
    (hB : tw.length = baseWidth p μ)
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) :
    letI : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
    letI : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
      ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
    let P := (e.map (loadValue source.zero (R + 1))).eval
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        runtimeBound R (baseWidth p 1) (baseWidth p μ)
          (SubexpPostfixControl.serializeCode SubexpRowPolynomialCalls.encode e.compile).length)
      (primitiveCfg program
        (physicalCfg (some program.entry) false false false
          (SubexpPostfixControl.serializeCode SubexpRowPolynomialCalls.encode e.compile) [] [] context))
      (primitiveCfg program
        ((⟨rf, Function.update (contextStore context) 87
          (SubexpCoefficientLiftArray.encodeArray
            (SubexpCoefficientLiftArray.liftedArray p μ source.modulus P)).reverse⟩ :
          State 16 256).withPC none)) := by
  let _ : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
  let _ : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
    ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  obtain ⟨rf, hr⟩ := run_bounded p μ source R sw tw frame context hμ H hz h74 h87 hB e
  exact ⟨rf, primitive_execution program hr⟩

/-- The stored target row has exactly the selected source cell count.
Zero padding is included in this physical byte length. -/
theorem output_length
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1))) :
    letI : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
    letI : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
      ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
    let P := (e.map (loadValue source.zero (R + 1))).eval
    (SubexpCoefficientLiftArray.encodeArray
      (SubexpCoefficientLiftArray.liftedArray p μ source.modulus P)).length =
        (R + 1) * (4 * baseWidth p μ) := by
  let _ : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
  let _ : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
    ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  let P := (e.map (loadValue source.zero (R + 1))).eval
  have hlen : P.length = R + 1 :=
    (SubexpRowPostfixBridge.validity p 1 source.modulus source.reduction source.zero
      (R + 1) source.program).eval_valid e
  change (SubexpRowPolynomialCalls.encode
    (SubexpCoefficientLiftArray.liftedArray p μ source.modulus P)).length = _
  rw [SubexpRowCost.encode_length]
  simp only [SubexpCoefficientLiftArray.liftedArray, List.length_map, hlen]

/-- The complete lifted array emitted by the preceding program is exactly
the polynomial section used in the layout. Arithmetic occurs in the source
field before the coefficient section is applied. -/
theorem output_denote (hμ : 0 < μ)
    (e : Algorithm.Expr (List (SubexpRowPolynomialCalls.Coefficient p 1)))
    (hdegree : ((e.map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ R) :
    letI : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
    letI : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
      ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
    let P := (e.map (loadValue source.zero (R + 1))).eval
    PolynomialAlgorithm.denote
      ((SubexpCoefficientLiftArray.liftedArray p μ source.modulus P).map
        (SubexpRowLiftSemantics.targetDecode p μ)) =
      SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R
        ((e.map (SubexpRowSourceSemantics.denote source)).eval) := by
  let _ : Add (List (SubexpRowPolynomialCalls.Coefficient p 1)) := ⟨addValue source.program⟩
  let _ : Mul (List (SubexpRowPolynomialCalls.Coefficient p 1)) :=
    ⟨mulValue p 1 source.modulus source.reduction source.zero (R + 1)⟩
  let P := (e.map (loadValue source.zero (R + 1))).eval
  have hlen : P.length = R + 1 :=
    (SubexpRowPostfixBridge.validity p 1 source.modulus source.reduction source.zero
      (R + 1) source.program).eval_valid e
  change PolynomialAlgorithm.denote
    ((SubexpCoefficientLiftArray.liftedArray p μ source.modulus P).map
      (SubexpRowLiftSemantics.targetDecode p μ)) = _
  rw [SubexpRowLiftSemantics.liftedArray_denote p μ source hμ R P hlen]
  congr 1
  exact SubexpRowSourceSemantics.eval_full_row_succ source R e hdegree

end SubexponentialSAT.SubexpRowToTaylor

end OAI.Algorithms
