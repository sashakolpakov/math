import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixContext
import OAI.Algorithms.SubexponentialSAT.SubexpDensePaddingSpec

namespace OAI.Algorithms

/-!
# Executing complete source-field row polynomials

Raw literals are padded to D coefficient cells. Addition and multiplication
are the concrete framed services, and multiplication retains D coefficients.
The final degree bound (D = R+1 for the application) restores the complete
source polynomial before any coefficientwise section into the lifted ring.
-/

namespace SubexponentialSAT.SubexpRowPostfixBridge

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPolynomialCalls (Coefficient encode)
open SubexpRowPostfixInterpreter (physicalCfg ImplementsOnGlobal LoadImplementsGlobal)
open SubexpRowPostfixContext (Ready operandStore)

def addValue {C : Type*} (ops : SubexpSymbolicCost.RingProgram C) (P Q : List C) : List C :=
  (SubexpDensePolynomial.addProgram ops P Q).1

def mulValue (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t z : Coefficient p μ) (D : ℕ) (P Q : List (Coefficient p μ)) : List (Coefficient p μ) :=
  SubexpTruncatedMultiply.result p μ M t z D P Q

def loadValue {C : Type*} (z : C) (D : ℕ) (P : List C) : List C :=
  SubexpDensePaddingSpec.padCells z D P

def addBound (p μ : ℕ) (ops : SubexpSymbolicCost.RingProgram (Coefficient p μ))
    (P Q : List (Coefficient p μ)) : ℕ :=
  31000 * (P.length + Q.length + 1) * (baseWidth p μ + 1)^2 +
    20 * ((encode P).length + (encode Q).length) + 8 * (encode (addValue ops P Q)).length + 69

def mulBound (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t z : Coefficient p μ) (D : ℕ) (P Q : List (Coefficient p μ)) : ℕ :=
  601000 * (D + 1)^3 * (baseWidth p μ + 1)^2 + 1 +
    20 * ((encode P).length + (encode Q).length) +
      8 * (encode (mulValue p μ M t z D P Q)).length + 69

def loadBound (p μ D : ℕ) (P : List (Coefficient p μ)) : ℕ :=
  12 * (encode P).length + 16 * (D * (4 * baseWidth p μ)) + 46

def program := SubexpRowPostfixInterpreter.globalProgram
  SubexpRowPolynomialCalls.addProgram SubexpRowPolynomialCalls.mulProgram
  SubexpDenseLiteralPadding.program

private theorem update_run {l : ℕ} (service : Program 16 256 l) (K : ℕ)
    (v p op : Bool) (code depth old new : List Bool) (context : Fin 252 → List Bool)
    (h : RunsIn service K
      ((⟨(physicalCfg (some service.entry) v p op code depth old context).regs,
        operandStore context code depth old⟩ : State 16 256).withPC (some service.entry))
      ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
        State 16 256).withPC none)) :
    RunsIn service K (physicalCfg (some service.entry) v p op code depth old context)
      (physicalCfg none false false false code depth new context) := by
  have he : ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
      State 16 256).withPC none) = physicalCfg none false false false code depth new context :=
    SubexpRowPostfixInterpreter.physicalCfg_after (some service.entry) v p op
      code depth old new context
  rw [he] at h
  exact h

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
variable (t z : Coefficient p μ) (D : ℕ)
variable (ops : SubexpSymbolicCost.RingProgram (Coefficient p μ))
variable (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
variable (H : Ready p μ M t z D width frame context)

include H in
theorem add_implements
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1) :
    ImplementsOnGlobal (fun P : List (Coefficient p μ) => P.length = D) encode
      (addValue ops) false SubexpRowPolynomialCalls.addProgram (addBound p μ ops) context := by
  intro P Q hP hQ xs code depth
  let operands := Encoding.encodeList encode (Q :: P :: xs)
  let tail := Encoding.encodeList encode xs
  let s := operandStore context code depth operands
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexpRowPostfixInterpreter.contextStore context i :=
    SubexpRowPostfixContext.operandStore_frame context code depth operands i h26 h28 h27
  apply update_run _ _ true true false code depth operands
    (Encoding.encodeList encode (addValue ops P Q :: xs)) context
  exact SubexpRowPolynomialCalls.add_runsIn p μ M s _ ops hadd P Q tail width frame
    H.positiveWidth H.widthLength rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.empty120)
    (by rw [hs 240 (by decide) (by decide) (by decide)]; exact H.empty240)
    (by rw [hs 241 (by decide) (by decide) (by decide)]; exact H.empty241)
    (by rw [hs 244 (by decide) (by decide) (by decide)]; exact H.empty244)
    (by rw [hs 245 (by decide) (by decide) (by decide)]; exact H.empty245)
    (Ready.prepared_addStore p μ M H code depth operands (encode P) (encode Q) tail)

include H in
theorem mul_implements :
    ImplementsOnGlobal (fun P : List (Coefficient p μ) => P.length = D) encode
      (mulValue p μ M t z D) true SubexpRowPolynomialCalls.mulProgram
      (mulBound p μ M t z D) context := by
  intro P Q hP hQ xs code depth
  let operands := Encoding.encodeList encode (Q :: P :: xs)
  let tail := Encoding.encodeList encode xs
  let s := operandStore context code depth operands
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexpRowPostfixInterpreter.contextStore context i :=
    SubexpRowPostfixContext.operandStore_frame context code depth operands i h26 h28 h27
  apply update_run _ _ true true true code depth operands
    (Encoding.encodeList encode (mulValue p μ M t z D P Q :: xs)) context
  exact SubexpRowPolynomialCalls.mul_runsIn p μ M s _ t z D P Q tail width frame hP hQ rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.empty120)
    (by rw [hs 240 (by decide) (by decide) (by decide)]; exact H.empty240)
    (by rw [hs 241 (by decide) (by decide) (by decide)]; exact H.empty241)
    (by rw [hs 244 (by decide) (by decide) (by decide)]; exact H.empty244)
    (Ready.prepared_mulStore p μ M H code depth operands (encode P) (encode Q) tail)
    (Ready.prepared_emptyBuffers p μ M H code depth operands (encode P) (encode Q) tail)
    (by rw [hs 121 (by decide) (by decide) (by decide)]; exact H.empty121)
    (by rw [hs 122 (by decide) (by decide) (by decide)]; exact H.empty122)
    (by rw [hs 245 (by decide) (by decide) (by decide)]; exact H.empty245)
    (by rw [hs 242 (by decide) (by decide) (by decide)]; exact H.zeroArray)
    (by rw [hs 243 (by decide) (by decide) (by decide)]; exact H.dimension)

omit [Fact p.Prime] in
theorem encode_zero_array (n : ℕ)
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p μ) false) :
    encode (List.replicate n z) = List.replicate (n * (4 * baseWidth p μ)) false := by
  induction n with
  | zero => simp [encode, SubexpConvolutionControl.encodeArray]
  | succ n ih =>
      change SubexpFlatAdd.encode z ++ encode (List.replicate n z) = _
      rw [hz, ih, ← List.replicate_add]
      congr 1
      ring

include H in
omit [Fact p.Prime] in
theorem load_implements
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p μ) false) :
    LoadImplementsGlobal (encode (p := p) (μ := μ)) (loadValue z D)
      SubexpDenseLiteralPadding.program (loadBound p μ D) context := by
  intro P xs code depth op
  let operands := Encoding.encodeList encode (P :: xs)
  let tail := Encoding.encodeList encode xs
  let s := operandStore context code depth operands
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexpRowPostfixInterpreter.contextStore context i :=
    SubexpRowPostfixContext.operandStore_frame context code depth operands i h26 h28 h27
  have hshape : s 242 = List.replicate (D * (4 * baseWidth p μ)) false := by
    rw [hs 242 (by decide) (by decide) (by decide), H.zeroArray, encode_zero_array p μ z D hz]
  have hpad : ModularArithmetic.padTo (s 242) (encode P) = encode (loadValue z D P) := by
    rw [hshape]
    exact SubexpDensePaddingSpec.padTo_encoded SubexpFlatAdd.encode z D
      (4 * baseWidth p μ) P hz (fun x _ => SubexpFlatAdd.encode_length x)
  apply update_run _ _ true false op code depth operands
    (Encoding.encodeList encode (loadValue z D P :: xs)) context
  have h := SubexpDenseLiteralPadding.program_runsIn s
    (physicalCfg (some SubexpDenseLiteralPadding.program.entry) true false op
      code depth operands context).regs (encode P) tail rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 99 (by decide) (by decide) (by decide)]; exact H.empty99)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.empty120)
  rw [hpad] at h
  rw [hshape] at h
  simpa only [s,operands,tail,Encoding.encodeList,List.length_replicate,
    loadBound] using h

theorem validity :
    letI : Add (List (Coefficient p μ)) := ⟨addValue ops⟩
    letI : Mul (List (Coefficient p μ)) := ⟨mulValue p μ M t z D⟩
    SubexpProjectedInterpreter.Validity
      (fun P : List (Coefficient p μ) => P.length = D) (loadValue z D) := by
  let _ : Add (List (Coefficient p μ)) := ⟨addValue ops⟩
  let _ : Mul (List (Coefficient p μ)) := ⟨mulValue p μ M t z D⟩
  constructor
  · intro P
    exact SubexpDensePaddingSpec.padCells_length z D P
  · intro P Q hP hQ
    change (SubexpDensePolynomial.addProgram ops P Q).1.length = D
    rw [SubexpPolynomialAddService.addProgram_length, hP, hQ, max_self]
  · intro P Q _ _
    exact SubexpTruncatedMultiply.result_length p μ M t z D P Q

include H in
/-- The physical program evaluates raw postfix literals using actual
source-ring arithmetic. Its only external hypotheses are stored data and
the literal zero encoding; there are no assumed arithmetic traces. -/
theorem run
    (hadd : ∀ a b, (ops.addRun a b).1 = (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p μ) false)
    (e : Algorithm.Expr (List (Coefficient p μ))) :
    letI : Add (List (Coefficient p μ)) := ⟨addValue ops⟩
    letI : Mul (List (Coefficient p μ)) := ⟨mulValue p μ M t z D⟩
    RunsIn program
      (SubexpProjectedInterpreter.exprCost encode (addBound p μ ops) (mulBound p μ M t z D)
        (loadValue z D) (loadBound p μ D) e + 5)
      (physicalCfg (some program.entry) false false false
        (SubexpPostfixControl.serializeCode encode e.compile) [] [] context)
      (physicalCfg none false false false []
        (SubexpPostfixControl.operandDepth [(e.map (loadValue z D)).eval])
        (Encoding.encodeList encode [(e.map (loadValue z D)).eval]) context) := by
  let _ : Add (List (Coefficient p μ)) := ⟨addValue ops⟩
  let _ : Mul (List (Coefficient p μ)) := ⟨mulValue p μ M t z D⟩
  exact SubexpRowPostfixInterpreter.global_complete_runsIn
    SubexpRowPolynomialCalls.addProgram SubexpRowPolynomialCalls.mulProgram
    SubexpDenseLiteralPadding.program encode (loadValue z D)
    (fun P : List (Coefficient p μ) => P.length = D)
    (addBound p μ ops) (mulBound p μ M t z D) (loadBound p μ D) context
    (add_implements p μ M t z D ops width frame context H hadd)
    (mul_implements p μ M t z D width frame context H)
    (load_implements p μ M t z D width frame context H hz)
    (validity p μ M t z D ops) e

end SubexponentialSAT.SubexpRowPostfixBridge

end OAI.Algorithms
