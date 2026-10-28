import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterLocalCall
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterCofactorView
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterScalarViews
import OAI.Algorithms.SubexponentialSAT.SubexpCRTAtZero

namespace OAI.Algorithms

/-! Full finite-machine execution of scalar CRT reconstruction. The local
correction, omitted-node cofactor, negation, Horner evaluation and weighted
addition are the concrete programs proved in the imported modules. -/

namespace SubexponentialSAT.SubexpCRTOuterExecution

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpCRTOuterProgram
open scoped BigOperators

attribute [local simp] Fin.coe_ofNat_eq_mod

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := SubexpPolynomialPowerProgram.Coefficient p (D + 1)
abbrev Poly := SubexpPolynomialPowerProgram.FixedPolynomial p (D + 1) D
abbrev Ring (c : Fin 4 → ZMod (p^(D + 1))) := SubexpLocalValueCorrectness.Ring p D c

noncomputable abbrev decode (c : Fin 4 → ZMod (p^(D + 1))) :=
  SubexpLocalValueCorrectness.decode p D c
noncomputable abbrev denote (c : Fin 4 → ZMod (p^(D + 1))) :=
  SubexpLocalValueCorrectness.denote p D c

omit [Fact p.Prime] in
theorem fixed_encode (P : Poly p D) :
    SubexpPolynomialPowerProgram.encode p (D + 1) P =
      SubexpHornerMachine.encodePolynomial p (D + 1) P.val := by
  have hf : (SubexpHornerMachine.flat : Coeff p D → List Bool) = SubexpFlatAdd.encode :=
    funext (fun x => SubexpHornerMachine.flat_eq_encode x)
  simp [SubexpPolynomialPowerProgram.encode, SubexpConvolutionControl.encodeArray,
    SubexpHornerMachine.encodePolynomial, List.flatMap, hf]

def middleBudget (Q : ℕ) (exponent : List Bool) : ℕ :=
  SubexpCRTOuterLocalCall.budget p D Q exponent +
  SubexpCRTOuterCofactorView.uniformBudget (baseWidth p (D + 1)) D Q +
  SubexpCRTOuterNeg.runtimeBound (baseWidth p (D + 1)) +
  SubexpCRTOuterHorner.budget D (baseWidth p (D + 1)) +
  SubexpCRTOuterAccumulate.runtimeBound (baseWidth p (D + 1))

noncomputable def term {Q : ℕ} (c : Fin 4 → ZMod (p^(D + 1)))
    (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (a : Fin Q → Ring p D c) (i : Fin Q) : Ring p D c :=
  (∏ j ∈ Finset.univ.erase i, (-decode p D c (nodes j))^D) *
    (TruncatedInverse.correction (fun j => decode p D c (nodes j)) D a
      (fun j => denote p D c (jets j)) i).eval (-decode p D c (nodes i))

/-- The actual middle of a loaded iteration. Its only mathematical premises
are the represented ring, residue-field and distinct-node facts needed for
local CRT inversion; the physical service inputs are proved from the literal
loaded store. -/
theorem middle_eval {Q : ℕ} (t z one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width exponent binaryD : List Bool)
    (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (hw : width.length = baseWidth p (D + 1))
    (hzcode : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false)
    (he : BinaryArithmetic.toNat binaryD = D) (hl : binaryD.length ≤ D)
    (hD : 0 < D) (c : Fin 4 → ZMod (p^(D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c one = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    {E : Type*} [Field E] [Fintype E] (ρ : Ring p D c →+* E)
    (q : ℕ) (hq : Fintype.card E = q) (π : Ring p D c)
    (hπ : π^(D + 1) = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hnodes : Function.Injective (fun j => ρ (decode p D c (nodes j))))
    (hexponent : BinaryArithmetic.toNat exponent = q - 2)
    (a : Fin Q → Ring p D c)
    (ha : ∀ i, a i * (TruncatedInverse.localFactor (fun j => decode p D c (nodes j)) D i).coeff 0 = 1)
    (processed remaining : List (Fin Q)) (current : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ current :: remaining)
    (acc : Coeff p D) (regs : Fin 16 → Bool) :
    ∃ n ≤ middleBudget p D Q exponent, ∃ rf b,
      Eval evaluateNode n
        ⟨regs, SubexpCRTOuterInput.loaded p D M t one minusOne width exponent binaryD
          nodes jets processed remaining current acc⟩
        ⟨rf, SubexpCRTOuterInput.loaded p D M t one minusOne width exponent binaryD
          nodes jets processed remaining current b⟩ ∧
      decode p D c b = decode p D c acc + term p D c nodes jets a current := by
  let s := SubexpCRTOuterInput.loaded p D M t one minusOne width exponent binaryD
    nodes jets processed remaining current acc
  let d : Data := ⟨regs, s⟩
  have hempty := SubexpCRTOuterScalarViews.loaded_empty p D M t one minusOne width exponent binaryD
    nodes jets processed remaining current acc
  have hindex : (List.replicate processed.length false).length = current.val := by
    simpa only [List.length_replicate] using traversal_index processed remaining current hfull
  have hlocal : ∀ j, d.stacks (localPorts j) =
      SubexpCRTCanonicalInput.canonical p D M t (nodes current) one minusOne width exponent
        (List.ofFn nodes) (List.replicate processed.length false) (jets current) j := by
    intro j
    exact congrFun (SubexpCRTOuterInput.loaded_local_store p D M t one minusOne width exponent binaryD
      nodes jets hw processed remaining current acc (fun _ => false)) j
  obtain ⟨n1, r1, W, hn1, h1, hW⟩ := SubexpCRTOuterLocalCall.command_eval p D M t z one
    minusOne width exponent nodes current (List.replicate processed.length false) (jets current)
    hw hzcode hindex hD c ht hz ho hminus ρ q hq π hπ hker hnodes hexponent
    (a current) (ha current) d hlocal
  let d1 : Data := ⟨r1, Function.update s 244 (SubexpPolynomialPowerProgram.encode p (D + 1) W)⟩
  change Eval localCorrection n1 d d1 at h1
  let base := SubexpCRTOuterCofactorView.words p D M t one minusOne width binaryD
  let frame := fun j => s (scalarPorts j)
  have hc := SubexpCRTOuterCofactorView.clean p D M t one minusOne width exponent binaryD
    nodes jets processed remaining current acc r1 (SubexpPolynomialPowerProgram.encode p (D + 1) W)
  have hs := SubexpCRTOuterCofactorView.prepared_view p D M t one minusOne width exponent binaryD
    nodes jets processed remaining current acc hw r1 (SubexpPolynomialPowerProgram.encode p (D + 1) W)
  obtain ⟨n2, r2, factor, hn2, h2, hf⟩ := SubexpCRTOuterCofactor.command_eval p (D + 1) M c t one
    minusOne ht ho hminus base frame rfl rfl rfl rfl hw
    (by simp [base, SubexpCRTOuterCofactorView.words])
    (by unfold baseWidth; positivity) ((remaining ++ processed).map nodes) d1 hc hs
  have hn2' : n2 ≤ SubexpCRTOuterCofactorView.uniformBudget (baseWidth p (D + 1)) D Q :=
    hn2.trans (SubexpCRTOuterCofactorView.budget_le p D M t one minusOne width exponent binaryD
      nodes jets processed remaining current acc hw he hl hfull r1
      (SubexpPolynomialPowerProgram.encode p (D + 1) W))
  have hfactor : decode p D c factor =
      ∏ j ∈ Finset.univ.erase current, (-decode p D c (nodes j))^D := by
    have hf' : decode p D c factor =
        ((remaining ++ processed).map (fun j => (-decode p D c (nodes j))^D)).prod := by
      simpa only [base, SubexpCRTOuterCofactorView.words, he, List.map_map,
        Function.comp_def, SubexpCRTCofactorMachine.decode, decode,
        SubexpLocalValueCorrectness.decode] using hf
    exact hf'.trans (cofactor_stream_product processed remaining current
      (fun j => (-decode p D c (nodes j))^D) hfull)
  let d2 : Data := ⟨r2, Function.update d1.stacks 262 (SubexpQuarticFlatMul.flat factor)⟩
  change Eval cofactor n2 d1 d2 at h2
  have hneg : ∀ i, d2.stacks (SubexpCRTOuterNeg.ports i) =
      SubexpCRTOuterNeg.blankStore minusOne.val M.bits width i := by
    intro i
    simp only [d2, d1, SubexpCRTOuterScalarViews.update_negation _ 262 _ (by decide),
      SubexpCRTOuterScalarViews.update_negation _ 244 _ (by decide)]
    exact SubexpCRTOuterScalarViews.negation_view p D M t one minusOne width exponent binaryD
      nodes jets processed remaining current acc i
  obtain ⟨n3, r3, hn3, h3⟩ := SubexpCRTOuterNeg.command_eval p (D + 1) M (nodes current)
    minusOne width hw d2
    (by
      simpa [d2, d1, s, SubexpCRTCofactorMachine.neg_flat_eq,
        SubexpCRTWeightedMachine.encode_eq_flat] using
        (SubexpCRTOuterScalarViews.loaded_current p D M t one minusOne width exponent binaryD
          nodes jets processed remaining current acc))
    hneg (by simpa [d2, d1, s] using hempty 263 (by decide))
    (by simpa [d2, d1, s] using hempty 318 (by decide))
    (by simpa [d2, d1, s] using hempty 319 (by decide))
  let negative := SubexpQuarticNegMachine.negateWords p (D + 1) M minusOne (nodes current)
  let d3 : Data := ⟨r3, Function.update d2.stacks 263 (SubexpQuarticFlatNeg.flat negative)⟩
  change Eval negativePoint n3 d2 d3 at h3
  have hhorner : ∀ i, d3.stacks (hornerPorts i) =
      if i = 77 ∨ i = 78 ∨ i = 79 then [] else SubexpHornerControl.store
        (SubexpHornerMachine.initialWordsWithCount p (D + 1) M t negative width W.val
          (List.replicate D true)) i := by
    intro i
    simp only [d3, d2, d1, SubexpCRTOuterScalarViews.update_horner _ 263 _ (by decide),
      SubexpCRTOuterScalarViews.update_horner _ 262 _ (by decide),
      SubexpCRTOuterScalarViews.update_horner _ 244 _ (by decide)]
    exact SubexpCRTOuterScalarViews.horner_view p D M t one minusOne width exponent binaryD
      nodes jets processed remaining current acc negative W.val (List.replicate D true) i
  obtain ⟨n4, hn4, r4, value, h4, hv⟩ := SubexpCRTOuterHorner.command_eval p (D + 1) M c t negative
    ht width hw W.val (List.replicate D true) (by simp [W.property]) d3
    (by simpa [d3, d2, d1] using fixed_encode p D W)
    (by simp [d3, SubexpCRTCofactorMachine.neg_flat_eq])
    (by
      simpa [d3, d2, d1, s] using
        (SubexpCRTOuterScalarViews.loaded_dimension p D M t one
          minusOne width exponent binaryD nodes jets processed remaining current acc))
    (by simpa [d3, d2, d1, s] using hempty 318 (by decide))
    (by simpa [d3, d2, d1, s] using hempty 319 (by decide))
    (by simpa [d3, d2, d1, s] using hempty 264 (by decide)) hhorner
  let d4 : Data := ⟨r4, Function.update (Function.update d3.stacks 244 []) 264
    (SubexpHornerMachine.flat value)⟩
  change Eval evaluateCorrection n4 d3 d4 at h4
  have hweighted : ∀ i, d4.stacks (scalarPorts i) =
      SubexpCRTCofactorControl.store frame (SubexpCRTOuterAccumulate.idleWords
        (SubexpCRTOuterScalarViews.weightedWords M.bits (SubexpQuarticFlatMul.flat t) width)) i := by
    intro i
    simp only [d4, d3, d2, d1, SubexpCRTOuterScalarViews.update_scalar _ 264 _ (by decide),
      SubexpCRTOuterScalarViews.update_scalar _ 244 _ (by decide),
      SubexpCRTOuterScalarViews.update_scalar _ 263 _ (by decide),
      SubexpCRTOuterScalarViews.update_scalar _ 262 _ (by decide)]
    exact SubexpCRTOuterScalarViews.weighted_view p D M t one minusOne width exponent binaryD
      nodes jets processed remaining current acc i
  obtain ⟨n5, r5, hn5, h5⟩ := SubexpCRTOuterAccumulate.command_eval p (D + 1) M t acc factor value
    frame (SubexpCRTOuterScalarViews.weightedWords M.bits (SubexpQuarticFlatMul.flat t) width)
    rfl rfl hw d4
    (by
      simpa [d4, d3, d2, d1, s, SubexpCRTWeightedMachine.encode_eq_flat] using
        (SubexpCRTOuterScalarViews.loaded_accumulator p D M t one minusOne width exponent binaryD
          nodes jets processed remaining current acc))
    (by simp [d4, d3, d2]) (by simp [d4])
    (by simp [d4, d3, SubexpQuarticFlatNeg.flat_length])
    (by simpa [d4, d3, d2, d1, s] using hempty 318 (by decide))
    (by simpa [d4, d3, d2, d1, s] using hempty 319 (by decide)) hweighted
  let b := SubexpCRTWeightedMachine.stepValue p (D + 1) M t acc factor value
  have hout : SubexpCRTOuterAccumulate.resultStacks d4.stacks (SubexpQuarticFlatMul.flat b) =
      SubexpCRTOuterInput.loaded p D M t one minusOne width exponent binaryD
        nodes jets processed remaining current b := by
    have h244 := hempty 244 (by decide)
    have h262 := hempty 262 (by decide)
    have h263 := hempty 263 (by decide)
    have h264 := hempty 264 (by decide)
    funext j
    by_cases hj244 : j = 244
    · subst j; simp [SubexpCRTOuterAccumulate.resultStacks, d4, d3, d2, d1, SubexpCRTOuterInput.loaded,
        sweepStore, initializedStacks, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store,
        SubexpCRTOuterInput.baseContext, SubexpCRTCanonicalInput.store]
    by_cases hj262 : j = 262
    · subst j; simp [SubexpCRTOuterAccumulate.resultStacks, d4, d3, d2, d1, SubexpCRTOuterInput.loaded,
        sweepStore, initializedStacks, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store]
    by_cases hj263 : j = 263
    · subst j; simp [SubexpCRTOuterAccumulate.resultStacks, d4, d3, d2, d1, SubexpCRTOuterInput.loaded,
        sweepStore, initializedStacks, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store]
    by_cases hj264 : j = 264
    · subst j; simp [SubexpCRTOuterAccumulate.resultStacks, d4, d3, d2, d1, SubexpCRTOuterInput.loaded,
        sweepStore, initializedStacks, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store]
    by_cases hj261 : j = 261
    · subst j
      simp [SubexpCRTOuterAccumulate.resultStacks, d4, d3, d2, d1,
        SubexpCRTOuterInput.loaded, sweepStore, loadedReady, loadedWords, readyWords,
        SubexpCRTWeightedMachine.encode_eq_flat]
    simp [SubexpCRTOuterAccumulate.resultStacks, d4, d3, d2, d1, s,
      SubexpCRTOuterInput.loaded, sweepStore, loadedReady, loadedWords, readyWords,
      hj244, hj262, hj263, hj264, hj261,
      SubexpCRTWeightedMachine.encode_eq_flat]
  rw [hout] at h5
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  refine ⟨n1 + (n2 + (n3 + (n4 + n5))), ?_, r5, b, hrun, ?_⟩
  · simp only [W.property] at hn4
    unfold middleBudget
    omega
  · have hnegative : decode p D c negative = -decode p D c (nodes current) :=
      SubexpCRTOuterNeg.negative_value p (D + 1) M (nodes current) minusOne hminus c
    have hvalue : decode p D c value = (denote p D c W).eval (decode p D c negative) := hv
    change decode p D c value =
      (SubexpLocalValueCorrectness.denote p D c W).eval (decode p D c negative) at hvalue
    rw [hW, hnegative] at hvalue
    rw [show decode p D c b = decode p D c acc + decode p D c factor * decode p D c value from
      SubexpCRTWeightedMachine.stepValue_decode p (D + 1) M c t acc factor value ht,
      hfactor, hvalue]
    rfl


/-- The complete command bound includes initialization, all Q measured
iterations and final cleanup. -/
def commandBudget (Q : ℕ) (exponent : List Bool) : ℕ :=
  controllerBudget (baseWidth p (D + 1)) D Q (middleBudget p D Q exponent)

/-- Actual complete outer execution from represented nodes and fixed-D jets.
The output is the scalar CRT reconstruction at zero, with no promised
arithmetic result among the premises. -/
theorem command_value {Q : ℕ} (t z one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width exponent : List Bool)
    (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (hw : width.length = baseWidth p (D + 1))
    (hzcode : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false)
    (hD : 0 < D) (c : Fin 4 → ZMod (p^(D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c one = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    {E : Type*} [Field E] [Fintype E] (ρ : Ring p D c →+* E)
    (q : ℕ) (hq : Fintype.card E = q) (π : Ring p D c)
    (hπ : π^(D + 1) = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hnodes : Function.Injective (fun j => ρ (decode p D c (nodes j))))
    (hexponent : BinaryArithmetic.toNat exponent = q - 2)
    (a : Fin Q → Ring p D c)
    (ha : ∀ i, a i * (TruncatedInverse.localFactor (fun j => decode p D c (nodes j)) D i).coeff 0 = 1)
    (regs : Fin 16 → Bool) :
    ∃ n ≤ commandBudget p D Q exponent, ∃ (out : Data) (b : Coeff p D),
      Eval command n (SubexpCRTOuterInput.data p D M t one minusOne width exponent nodes jets regs) out ∧
      out.stacks 261 = SubexpFlatAdd.encode b ∧
      decode p D c b = SubexpCRTAtZero.value (fun i => decode p D c (nodes i)) D a
        (fun i => denote p D c (jets i)) := by
  let d := SubexpCRTOuterInput.data p D M t one minusOne width exponent nodes jets regs
  have hwidth : d.stacks 202 = width := by
    simp [d, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store,
      SubexpCRTOuterInput.baseContext, SubexpCRTCanonicalInput.store,
      SubexpQuarticFlatMul.bankStore]
  obtain ⟨n, hn, out, b, heval, hout, hvalue⟩ := controller_run
    (fun i => SubexpFlatAdd.encode (nodes i))
    (fun i => SubexpPolynomialPowerProgram.encode p (D + 1) (jets i))
    SubexpFlatAdd.encode (decode p D c) (term p D c nodes jets a) evaluateNode
    d D (middleBudget p D Q exponent) (List.finRange Q) z
    (by simp [d, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store,
      SubexpCRTOuterInput.baseContext, SubexpCRTCanonicalInput.store])
    (SubexpCRTOuterInput.clean p D M t one minusOne width exponent nodes jets)
    (by intro i; simp [hwidth, hw])
    (by intro i; simp [hwidth, hw])
    (by rw [hwidth, hw]; unfold baseWidth; positivity)
    (by simp [d, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store])
    (by simp [d, SubexpCRTOuterInput.data, SubexpCRTOuterInput.store])
    (by simpa only [hwidth, hw] using hzcode) hz
    (by
      intro binaryD he hl processed remaining current acc hfull rr
      exact middle_eval p D M t z one minusOne width exponent binaryD nodes jets hw hzcode he hl
        hD c ht hz ho hminus ρ q hq π hπ hker hnodes hexponent a ha
        processed remaining current hfull acc rr)
  refine ⟨n, ?_, out, b, heval, hout, hvalue.trans ?_⟩
  · simpa only [commandBudget, hwidth, hw, List.length_finRange] using hn
  · rw [SubexpCRTAtZero.value_scalar_cofactors]
    change ((List.finRange Q).map (term p D c nodes jets a)).sum =
      ∑ i, term p D c nodes jets a i
    rw [← List.ofFn_eq_map, List.sum_ofFn]

/-- Include the final halt of the single finite instruction table. -/
theorem program_value {Q : ℕ} (t z one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width exponent : List Bool)
    (nodes : Fin Q → Coeff p D) (jets : Fin Q → Poly p D)
    (hw : width.length = baseWidth p (D + 1))
    (hzcode : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false)
    (hD : 0 < D) (c : Fin 4 → ZMod (p^(D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c one = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    {E : Type*} [Field E] [Fintype E] (ρ : Ring p D c →+* E)
    (q : ℕ) (hq : Fintype.card E = q) (π : Ring p D c)
    (hπ : π^(D + 1) = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hnodes : Function.Injective (fun j => ρ (decode p D c (nodes j))))
    (hexponent : BinaryArithmetic.toNat exponent = q - 2)
    (a : Fin Q → Ring p D c)
    (ha : ∀ i, a i * (TruncatedInverse.localFactor (fun j => decode p D c (nodes j)) D i).coeff 0 = 1)
    (regs : Fin 16 → Bool) :
    ∃ (out : Data) (b : Coeff p D),
      RunsIn program (commandBudget p D Q exponent + 1)
        ((SubexpCRTOuterInput.data p D M t one minusOne width exponent nodes jets regs).withPC
          (some program.entry)) (out.withPC none) ∧
      out.stacks 261 = SubexpFlatAdd.encode b ∧
      decode p D c b = SubexpCRTAtZero.value (fun i => decode p D c (nodes i)) D a
        (fun i => denote p D c (jets i)) := by
  obtain ⟨n, hn, out, b, heval, hout, hvalue⟩ := command_value p D M t z one minusOne width exponent
    nodes jets hw hzcode hD c ht hz ho hminus ρ q hq π hπ hker hnodes hexponent a ha regs
  exact ⟨out, b, ⟨n + 1, Nat.add_le_add_right hn 1,
    compiled_halt_trace heval 256 261⟩, hout, hvalue⟩

end SubexponentialSAT.SubexpCRTOuterExecution

end OAI.Algorithms
