import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalReadiness
import OAI.Algorithms.SubexponentialSAT.SubexpLocalValueCorrectness

namespace OAI.Algorithms

/-! Composition of the physical per-node CRT stages. The input predicate
describes concrete words, metadata, and empty scratch. The full arithmetic
schedule is executed before the scratch is cleared. -/

namespace SubexponentialSAT.SubexpLocalCRTExecution

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

structure Input (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    (nodes : List (Coeff p D)) (index : List Bool) (J : Poly p D) : Prop where
  scan : SubexpLocalProductScan.Ready p D M (SubexpLocalInitializedScan.initial p D s)
    t z theta one minusOne width frame
  native : ∀ i, s (SubexpLocalSeedProgram.powerPorts (SubexpQuarticPowerProgram.native i)) =
    SubexpQuarticPowerProgram.cleanNative M.bits (SubexpFlatAdd.encode t) width i
  negation : ∀ i, s (SubexpLocalLinearFactorProgram.negatePorts i) =
    SubexpLocalSeedProgram.blankNegation minusOne.val M.bits width i
  empty : ∀ i ∈ SubexpLocalCRTFrames.scratch, s i = []
  dimension : s 243 = List.replicate D true
  zeroCell : s 104 = List.replicate (4 * baseWidth p (D + 1)) false
  zeroCode : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false
  one : s 207 = SubexpFlatAdd.encode one
  nodes : s 214 = nodes.flatMap SubexpFlatAdd.encode
  index : s 216 = index
  jet : s 225 = encode p (D + 1) J

def onePolynomial (z one : Coeff p D) : Poly p D :=
  SubexpLocalValueCorrectness.constant p D z one

def localProduct (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (nodes : List (Coeff p D)) (index : List Bool) : Poly p D :=
  (SubexpNodeScanControl.run (SubexpLocalProductScan.stepValue p D M t z theta one minusOne)
    nodes ⟨onePolynomial p D z one, index, true⟩).value

def correctionValue (t z one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (P J : Poly p D) (seed : Coeff p D) : Poly p D :=
  let O := onePolynomial p D z one
  let Z := SubexpLocalValueCorrectness.zero p D z
  let Cb := SubexpLocalValueCorrectness.constant p D z seed
  let N := SubexpLocalValueCorrectness.constant p D z
    (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne seed)
  let F := SubexpLocalGeometricProgram.defect p D M t z one P N O
  next p (D + 1) M t z J (SubexpLocalGeometricProgram.inverseValue p D M t z one F O Z Cb)

def scratchBound (Q D B I : ℕ) : ℕ := (Q + D + 1) * (4 * B + 1) + I

def runtimeBound (Q D B I : ℕ) (exponent : List Bool) : ℕ :=
  (500 * (D + 1) * (B + 1) + 7 * (Q * (4 * B) + I) + 20 +
    (Q * (700000 * (D + 1)^4 * (B + 1)^2 + 18 * (4 * B) + 28) + 2)) +
  (SubexpQuarticPowerProgram.runtimeBound B exponent + 26000 * (D + 1) * (B + 1)^2) +
  3500000 * (D + 1)^4 * (B + 1)^2 + 37 * (2 * scratchBound Q D B I + 3)

omit [Fact p.Prime] in
theorem one_encoding (s : Store) (z one : Coeff p D)
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false)
    (ho : s 207 = SubexpFlatAdd.encode one) :
    SubexpLocalCRTSetup.oneArray D (baseWidth p (D + 1)) (s 207) =
      encode p (D + 1) (onePolynomial p D z one) := by
  change SubexpLocalCRTSetup.oneArray D (baseWidth p (D + 1)) (s 207) =
    SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode
      (SubexpLocalCorrectionAlgebra.padded z one z D)
  rw [SubexpLinearFactorEncoding.encode_padded _ z one z _ D hz]
  simp [SubexpLocalCRTSetup.oneArray, hz, ho]

omit [Fact p.Prime] in
theorem zero_encoding (z : Coeff p D)
    (hz : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false) :
    SubexpLocalCRTSetup.zeroArray D (baseWidth p (D + 1)) =
      encode p (D + 1) (SubexpLocalValueCorrectness.zero p D z) := by
  simp [encode, SubexpLocalValueCorrectness.zero, SubexpConvolutionControl.encodeArray, hz]

omit [Fact p.Prime] in
theorem flatMap_length (nodes : List (Coeff p D)) :
    (nodes.flatMap SubexpFlatAdd.encode).length = nodes.length * (4 * baseWidth p (D + 1)) := by
  induction nodes with
  | nil => simp
  | cons a nodes ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem scratchBound_lower (Q D B I : ℕ) :
    D * (4 * B) ≤ scratchBound Q D B I ∧
    Q * (4 * B) ≤ scratchBound Q D B I ∧
    4 * B ≤ scratchBound Q D B I ∧
    I ≤ scratchBound Q D B I ∧ 1 ≤ scratchBound Q D B I := by
  unfold scratchBound
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem runtimeBound_le (Q D B I : ℕ) (exponent : List Bool) (hI : I ≤ Q) :
    runtimeBound Q D B I exponent ≤
      SubexpQuarticPowerProgram.runtimeBound B exponent +
        5000000 * (Q + 1) * (D + 1)^4 * (B + 1)^2 := by
  unfold runtimeBound scratchBound
  ring_nf
  omega

theorem positive_value (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    (nodes : List (Coeff p D)) (index : List Bool) (J : Poly p D)
    (H : Input p D M s t z theta one minusOne width frame nodes index J)
    (hD : 0 < D) (c : Fin 4 → ZMod (p^(D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (ho : quotientDenote c (one.map (wordValue p (D + 1))) = 1)
    (regs : Fin 16 → Bool) :
    ∃ n regs' seed,
      n ≤ runtimeBound nodes.length D (baseWidth p (D + 1)) index.length (s 206) ∧
      Eval SubexpLocalCRTProgram.positiveDimension n ⟨regs, s⟩
        ⟨regs', Function.update s 244 (encode p (D + 1)
          (correctionValue p D M t z one minusOne
            (localProduct p D M t z theta one minusOne nodes index) J seed))⟩ ∧
      quotientDenote c (seed.map (wordValue p (D + 1))) =
        (SubexpLocalValueCorrectness.denote p D c
          (localProduct p D M t z theta one minusOne nodes index)).coeff 0 ^
            BinaryArithmetic.toNat (s 206) := by
  let B := baseWidth p (D + 1)
  let O := onePolynomial p D z one
  let Z := SubexpLocalValueCorrectness.zero p D z
  let P := localProduct p D M t z theta one minusOne nodes index
  let scanned := SubexpLocalInitializedScan.output p D M s t z theta one minusOne nodes index O
  have hO := one_encoding p D s z one H.zeroCode H.one
  have hZ := zero_encoding p D z H.zeroCode
  have hscan := SubexpLocalInitializedScan.command_value p D M s t z theta one minusOne width frame
    nodes index O H.scan H.dimension H.zeroCell (by simp [H.one]) hO H.nodes H.index
    (fun j hj => H.empty j (SubexpLocalReadiness.initialization_work_mem j hj))
  obtain ⟨n₀, r₀, hn₀, he₀⟩ := hscan regs
  have hP : P.val ≠ [] := by
    intro he
    have hl := P.property
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  obtain ⟨a, tail, hcons⟩ := List.exists_cons_of_ne_nil hP
  have htail : tail.length + 1 = D := by simpa [hcons] using P.property
  have hseedReady := SubexpLocalReadiness.seed_scanned p D M s t z theta one a minusOne width
    nodes index O tail hcons H.scan.multiply.scalarWidthLength H.native H.negation
    H.one H.dimension H.zeroCell H.empty
  obtain ⟨n₁, r₁, seed, hn₁, he₁, hv⟩ := SubexpLocalSeedProgram.command_typed_eval
    p (D + 1) M scanned D tail htail c t a one minusOne width width ht ho hseedReady r₀
  let Cb := SubexpLocalValueCorrectness.constant p D z seed
  let N := SubexpLocalValueCorrectness.constant p D z
    (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne seed)
  let seeded := SubexpLocalSeedProgram.prepared scanned D B (SubexpFlatAdd.encode a)
    (SubexpFlatAdd.encode seed)
    (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne seed))
  have hsframe (j : Fin 256) (hj : j ∉ SubexpLocalInitializedScan.changed) : scanned j = s j :=
    SubexpLocalInitializedScan.output_frame p D M s t z theta one minusOne nodes index O
      (H.empty 218 (by decide)) (H.empty 219 (by decide)) j hj
  have hgReady := SubexpLocalReadiness.geometric_seed p D M scanned t width frame
    (SubexpLocalReadiness.geometric_scanned p D M s t z theta one minusOne width frame
      nodes index O H.scan) (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode seed)
    (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne seed))
  have hSeedEncoding : SubexpLocalSeedProgram.constantArray D B (SubexpFlatAdd.encode seed) =
      encode p (D + 1) Cb := SubexpLocalSeedProgram.constantArray_encodes p (D + 1) D z seed H.zeroCode
  have hNegativeEncoding : SubexpLocalSeedProgram.constantArray D B
      (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne seed)) =
      encode p (D + 1) N := SubexpLocalSeedProgram.constantArray_encodes p (D + 1) D z _ H.zeroCode
  have hg := SubexpLocalGeometricProgram.command_value p D M seeded t z one P N Cb O Z J
    width frame hgReady
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished,
      scanned, P, localProduct, O])
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished, hNegativeEncoding])
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished, hSeedEncoding])
    (by simpa [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished, scanned] using hO)
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished,
      hsframe 225 (by decide), H.jet])
    (by simpa [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished, scanned,
      Z, SubexpLocalValueCorrectness.zero, encode] using hZ)
    (by simpa [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished, scanned] using hZ)
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished,
      hsframe 243 (by decide), H.dimension])
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished,
      hsframe 222 (by decide), H.empty 222 (by decide)])
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished,
      hsframe 241 (by decide), H.empty 241 (by decide)])
    (by simp [seeded, SubexpLocalSeedProgram.prepared, SubexpLocalSeedProgram.finished,
      hsframe 246 (by decide), H.empty 246 (by decide)])
  obtain ⟨n₂, r₂, hn₂, he₂⟩ := hg r₁
  let resultStore := SubexpLocalGeometricProgram.output p D M seeded t z one P N Cb O Z J
  let W := correctionValue p D M t z one minusOne P J seed
  have hresult : resultStore 244 = encode p (D + 1) W := by
    simp [resultStore, SubexpLocalGeometricProgram.output, W, correctionValue, O, Z, N, Cb]
  have hframe : SubexpLocalCRTFrames.Frame s resultStore := by
    apply SubexpLocalCRTFrames.frame_update _ 244 _ (by decide)
    apply SubexpLocalCRTFrames.frame_update _ 241 _ (by decide)
    apply SubexpLocalCRTFrames.frame_update _ 240 _ (by decide)
    apply SubexpLocalCRTFrames.frame_update _ 222 _ (by decide)
    apply SubexpLocalCRTFrames.frame_update _ 228 _ (by decide)
    apply SubexpLocalCRTFrames.frame_update _ 227 _ (by decide)
    apply SubexpLocalCRTFrames.frame_update _ 208 _ (by decide)
    apply SubexpLocalCRTFrames.frame_update _ 205 _ (by decide)
    apply SubexpLocalCRTFrames.frame_node_work
    exact SubexpLocalCRTFrames.frame_initialized s D B
  let L := scratchBound nodes.length D B index.length
  have hlow := scratchBound_lower nodes.length D B index.length
  have hZlen : (SubexpLocalCRTSetup.zeroArray D B).length = D * (4 * B) := by simp
  have hOlen : (SubexpLocalCRTSetup.oneArray D B (s 207)).length = D * (4 * B) := by
    rw [hO, encode_length]
  have hnodeslen : (s 214).length = nodes.length * (4 * B) := by
    rw [H.nodes, flatMap_length]
  have hinitBound : SubexpLocalCRTFrames.Bounded (SubexpLocalInitializedScan.initial p D s) L :=
    SubexpLocalCRTFrames.bounded_initialized s D B L
      (SubexpLocalCRTFrames.bounded_of_empty s L H.empty)
      (by rw [hZlen]; exact hlow.1) (by rw [hOlen]; exact hlow.1)
      (by rw [hnodeslen]; exact hlow.2.1)
      (by simpa [H.index] using hlow.2.2.2.1) hlow.2.2.2.2
  have hscanBound : SubexpLocalCRTFrames.Bounded scanned L := by
    apply SubexpLocalCRTFrames.bounded_node_work hinitBound
    intro j
    fin_cases j
    · simp [SubexpNodeScanControl.words]
    · exact (SubexpLocalCRTFrames.node_skip_length _ nodes ⟨O, index, true⟩).trans hlow.2.2.2.1
    · exact (SubexpLocalCRTFrames.marker_length _).trans hlow.2.2.2.2
    · simpa [SubexpNodeScanControl.words, encode_length] using hlow.1
    · simp [SubexpNodeScanControl.words]
    · simp [SubexpNodeScanControl.words]
  have hseedBound : SubexpLocalCRTFrames.Bounded seeded L := by
    apply SubexpLocalCRTFrames.bounded_update _ 228 _
      (by rw [hNegativeEncoding, encode_length]; exact hlow.1)
    apply SubexpLocalCRTFrames.bounded_update _ 227 _
      (by rw [hSeedEncoding, encode_length]; exact hlow.1)
    apply SubexpLocalCRTFrames.bounded_update _ 208 _
      (by simpa using hlow.2.2.1)
    exact SubexpLocalCRTFrames.bounded_update hscanBound 205 _ (by simpa using hlow.2.2.1)
  have hbound : SubexpLocalCRTFrames.Bounded resultStore L := by
    apply SubexpLocalCRTFrames.bounded_update _ 244 _ (by simpa using hlow.1)
    apply SubexpLocalCRTFrames.bounded_update _ 241 _ (by simpa using hlow.1)
    apply SubexpLocalCRTFrames.bounded_update _ 240 _ (by simpa using hlow.1)
    exact SubexpLocalCRTFrames.bounded_update hseedBound 222 _ (by simpa using hlow.1)
  have hc := SubexpLocalCRTFrames.command_run s resultStore L hframe H.empty hbound
  obtain ⟨n₃, r₃, hn₃, he₃⟩ := hc r₂
  rw [hresult] at he₃
  refine ⟨n₀ + (n₁ + (n₂ + n₃)), r₃, seed, ?_, he₀.seq (he₁.seq (he₂.seq he₃)), ?_⟩
  · rw [hnodeslen] at hn₀
    have hexponent : scanned 206 = s 206 := hsframe 206 (by decide)
    rw [hexponent] at hn₁
    dsimp only [L, B] at hn₀ hn₁ hn₂ hn₃
    unfold runtimeBound
    omega
  · have hconstant : (SubexpLocalValueCorrectness.denote p D c P).coeff 0 =
        quotientDenote c (a.map (wordValue p (D + 1))) := by
      simp [SubexpLocalValueCorrectness.denote, SubexpLocalValueCorrectness.decode,
        hcons, PolynomialAlgorithm.denote_cons]
    rw [hconstant]
    simpa only [hsframe 206 (by decide)] using hv

theorem positive_correct (s : Store) (t z one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    {Q : ℕ} (nodes : Fin Q → Coeff p D) (i : Fin Q) (index : List Bool) (J : Poly p D)
    (H : Input p D M s t z (nodes i) one minusOne width frame (List.ofFn nodes) index J)
    (hindex : index.length = i.val) (hD : 0 < D)
    (c : Fin 4 → ZMod (p^(D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : SubexpLocalValueCorrectness.decode p D c z = 0)
    (ho : SubexpLocalValueCorrectness.decode p D c one = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    {E : Type*} [Field E] [Fintype E]
    (ρ : SubexpLocalValueCorrectness.Ring p D c →+* E)
    (q : ℕ) (hq : Fintype.card E = q)
    (π : SubexpLocalValueCorrectness.Ring p D c) (hπ : π^(D + 1) = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hnodes : Function.Injective (fun j => ρ (SubexpLocalValueCorrectness.decode p D c (nodes j))))
    (hexponent : BinaryArithmetic.toNat (s 206) = q - 2)
    (a : SubexpLocalValueCorrectness.Ring p D c)
    (ha : a * (TruncatedInverse.localFactor
      (fun j => SubexpLocalValueCorrectness.decode p D c (nodes j)) D i).coeff 0 = 1)
    (regs : Fin 16 → Bool) :
    ∃ n regs', ∃ W : Poly p D,
      n ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p (D + 1)) (s 206) +
        5000000 * (Q + 1) * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2 ∧
      Eval SubexpLocalCRTProgram.positiveDimension n ⟨regs, s⟩
        ⟨regs', Function.update s 244 (encode p (D + 1) W)⟩ ∧
      SubexpLocalValueCorrectness.denote p D c W =
        TruncatedInverse.correctedJet
          (TruncatedInverse.localFactor (fun j => SubexpLocalValueCorrectness.decode p D c (nodes j)) D i)
          (SubexpLocalValueCorrectness.denote p D c J) a D := by
  obtain ⟨n, rf, seed, hn, he, hv⟩ := positive_value p D M s t z (nodes i) one minusOne
    width frame (List.ofFn nodes) index J H hD c ht ho regs
  let P := localProduct p D M t z (nodes i) one minusOne (List.ofFn nodes) index
  let W := correctionValue p D M t z one minusOne P J seed
  let L := TruncatedInverse.localFactor (fun j => SubexpLocalValueCorrectness.decode p D c (nodes j)) D i
  have hP : SubexpLocalValueCorrectness.denote p D c P = Truncation.trunc D L :=
    SubexpLocalValueCorrectness.nodeScan_localFactor p D M c t z one minusOne
      ht hz ho hminus nodes i index hindex
  have hseed : SubexpLocalValueCorrectness.decode p D c seed = L.coeff 0 ^ (q - 2) := by
    change SubexpLocalValueCorrectness.decode p D c seed =
      (SubexpLocalValueCorrectness.denote p D c P).coeff 0 ^ BinaryArithmetic.toNat (s 206) at hv
    rw [hP, Truncation.coeff_trunc, ite_eq_left hD, hexponent] at hv
    exact hv
  have hnonzero : ρ (L.coeff 0) ≠ 0 :=
    SubexpLocalFactorAlgebra.residue_localFactor_coeff_ne_zero ρ _ hnodes D i
  have hnil : (1 - SubexpLocalValueCorrectness.decode p D c seed * L.coeff 0)^(D + 1) = 0 := by
    rw [hseed]
    simpa only [mul_comm] using SubexpResidueInverse.fermat_defect_nilpotent
      ρ q hq π (D + 1) hπ hker (L.coeff 0) hnonzero
  refine ⟨n, rf, W, ?_, he, ?_⟩
  · have hb := runtimeBound_le Q D (baseWidth p (D + 1)) index.length (s 206)
      (by rw [hindex]; exact Nat.le_of_lt i.isLt)
    have hn' : n ≤ runtimeBound Q D (baseWidth p (D + 1)) index.length (s 206) := by
      simpa using hn
    exact hn'.trans hb
  · exact SubexpLocalValueCorrectness.correction_denote p D M c t z one seed minusOne
      ht hz ho hminus P J L a hP ha hnil

omit [Fact p.Prime] in
/-- Lift the concrete positive-dimension endpoint through the controller's
actual dimension guard. This adds exactly the test/branch overhead. -/
theorem command_of_positive (s : Store) (K : ℕ) (property : Poly p D → Prop)
    (hD : 0 < (s 243).length)
    (h : ∀ regs : Fin 16 → Bool, ∃ n regs', ∃ W : Poly p D, n ≤ K ∧
      Eval SubexpLocalCRTProgram.positiveDimension n ⟨regs, s⟩
        ⟨regs', Function.update s 244 (encode p (D + 1) W)⟩ ∧ property W)
    (regs : Fin 16 → Bool) :
    ∃ n regs', ∃ W : Poly p D, n ≤ K + 2 ∧
      Eval SubexpLocalCRTProgram.command n ⟨regs, s⟩
        ⟨regs', Function.update s 244 (encode p (D + 1) W)⟩ ∧ property W := by
  let d : Data := ⟨regs, s⟩
  obtain ⟨n, rf, W, hn, he, hp⟩ := h (testResult 243 15 d).regs
  have hg : (testResult 243 15 d).regs 15 = true := by
    rw [testResult_flag]
    exact decide_eq_true hD
  exact ⟨1 + (n + 1), rf, W, by omega, (test_eval 243 15 d).seq (.ite_true hg he), hp⟩

theorem command_zero (s : Store) (hD : s 243 = []) :
    ExecutesIn SubexpLocalCRTProgram.command 2 s s := by
  exact SubexpNodeScanControl.branch_false 243 15 SubexpLocalCRTProgram.positiveDimension
    (.base .skip) 0 s s hD (fun regs => ⟨0, regs, by simp, .base (.skip _)⟩)

theorem program_trace {n : ℕ} {d e : Data}
    (he : Eval SubexpLocalCRTProgram.command n d e) :
    Trace SubexpLocalCRTProgram.program (n + 1)
      (d.withPC (some SubexpLocalCRTProgram.program.entry)) (e.withPC none) :=
  compiled_halt_trace he 225 244

theorem program_primitive {n K : ℕ} {d e : Data}
    (he : Eval SubexpLocalCRTProgram.command n d e) (hn : n ≤ K) :
    Computation.RunsIn (primitive SubexpLocalCRTProgram.program).step
      (primitiveOverhead SubexpLocalCRTProgram.program * (K + 1))
      (primitiveCfg SubexpLocalCRTProgram.program (d.withPC (some SubexpLocalCRTProgram.program.entry)))
      (primitiveCfg SubexpLocalCRTProgram.program (e.withPC none)) := by
  obtain ⟨steps, hsteps, ht⟩ := primitive_trace SubexpLocalCRTProgram.program (program_trace he)
  exact ⟨steps, hsteps.trans (Nat.mul_le_mul_left _ (by omega)), ht⟩

end SubexponentialSAT.SubexpLocalCRTExecution

end OAI.Algorithms
