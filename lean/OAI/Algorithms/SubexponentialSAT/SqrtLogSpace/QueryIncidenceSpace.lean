import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryIncidenceCommand
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStoredLow
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLowBounds
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

noncomputable section
variable {R : Type*} [CommRing R]

/-- Each emitted incidence stream has only one constant record and one row of
positive Taylor coefficients per ambient coordinate. This is polynomial storage
before specialization, independently of the support-universe cardinality. -/
theorem incidence_entries_length {n B d : ℕ}
    (ops : SubexpSymbolicCost.RingProgram (RingProgram.Code (Word B) d))
    (J : ℕ) (theta beta : RingProgram.Code (Word B) d)
    (rows : Fin n → List (RingProgram.Code (Word B) d)) :
    (PerturbationAssembly.outputWords ops J theta beta rows).length =
      1 + n * (J - 1) := by
  have htail (v : Fin n) :
      (PerturbationAssembly.shiftedValue ops J theta (rows v)).val.tail.length = J - 1 := by
    rw [List.length_tail, (PerturbationAssembly.shiftedValue ops J theta (rows v)).property]
  simp [PerturbationAssembly.outputWords, PerturbationAssembly.rawWords,
    List.length_flatten, List.map_ofFn, List.sum_ofFn, htail, Nat.add_comm]


/-- The emitted dictionary has the same bounded keys as its decoded source;
this premise is obtained from the actual incidence constructor. -/
theorem incidence_valid {n B d : ℕ}
    (ops : SubexpSymbolicCost.RepresentedRing (RingProgram.Code (Word B) d) R)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta beta : RingProgram.Code (Word B) d)
    (rows : Fin n → List (RingProgram.Code (Word B) d)) :
    ∀ a ∈ PerturbationAssembly.outputWords ops.program J theta beta rows,
      Product.ValidKey Finset.univ u J a.1 := by
  intro a ha
  apply PerturbationAssembly.outputWords_valid ops u J hu hJ theta beta rows a.1
  simp only [Squarefree.Sparse.keys, PerturbationProgram.decodeRecords,
    List.map_map, Function.comp_def]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- Source storage before specialization is polynomial even though later
multivariate products would have exponentially many potential supports. -/
theorem incidence_bytes_length {n B d : ℕ}
    (ops : SubexpSymbolicCost.RepresentedRing (RingProgram.Code (Word B) d) R)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta beta : RingProgram.Code (Word B) d)
    (rows : Fin n → List (RingProgram.Code (Word B) d)) :
    (Product.bytes (PerturbationAssembly.outputWords ops.program J theta beta rows)).length ≤
      (1 + n * (J - 1)) * (2 * (u + J + n) + 2 * (d * B) + 2) := by
  have h := Product.bytes_length_le
    (PerturbationAssembly.outputWords ops.program J theta beta rows) (u + J + n)
    (fun a ha => Squarefree.encodeIndex_length_le a.1
      (incidence_valid ops u J hu hJ theta beta rows a ha).1)
  rwa [incidence_entries_length] at h

/-- Existing clipping of an incidence row does not change any retained scalar
coefficient after the immediate correction substitution. -/
theorem dense_eval_canonical {n : ℕ} (u J : ℕ) (U : Finset (Fin n))
    (P : Squarefree.Jet (Fin n) R) :
    Dense.ofPolynomial u J (Moments.jetEval
      (fun v => if v ∈ U then (1 : R) else 0)
      (by intro v; split <;> simp) (Squarefree.canonical u J P)) =
      Dense.ofPolynomial u J (Moments.jetEval
        (fun v => if v ∈ U then (1 : R) else 0)
        (by intro v; split <;> simp) P) := by
  ext i j
  simp [Dense.coeff_ofPolynomial, Moments.jetEval,
    Squarefree.coeff_canonical, i.isLt, j.isLt]

/-- Closed incidence meaning for the exact normalizer output: the dictionary
comes from the executed origin/singleton emitter, and all duplicate scalar keys
are added before later factor multiplication. -/
theorem normalized_incidence_dense (t : ℕ) (ht : 0 < t) {n d : ℕ}
    (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J) (U : Finset (Fin n))
    (theta beta : RingProgram.Code (Word (baseWidth 3 t)) d)
    (rows : Fin n → List (RingProgram.Code (Word (baseWidth 3 t)) d)) :
    let ops := RingProgram.modelRing t ht hd model M cache
    let source := PerturbationAssembly.outputWords ops.program J theta beta rows
    TruncatedRingProgram.rawValue u J ops.decode
      (Normalize.run 3 t M cache (HeadEvaluation.specializeEntries U source) []) =
      Dense.ofPolynomial u J (Moments.jetEval
        (fun v => if v ∈ U then (1 : model.O t) else 0)
        (by intro v; split <;> simp)
        (Moments.incidenceJet (fun v => PerturbationProgram.polynomial ops (rows v))
          (ops.decode theta) (ops.decode beta))) := by
  dsimp only
  have hn := normalized_specialization_dense 3 t M cache
    (LiftRing.of (model.F t)) (RingBasis.basis (model.F t)) u J U
    (PerturbationAssembly.outputWords (RingProgram.modelProgram t model M cache)
      J theta beta rows)
  change TruncatedRingProgram.rawValue u J
    (RingProgram.modelRing t ht hd model M cache).decode _ = _ at hn
  rw [RingProgram.modelRing_program, hn]
  have hs := PerturbationAssembly.outputWords_denote
    (RingProgram.modelRing t ht hd model M cache) u J hu hJ theta beta rows
  change rawDenote (RingProgram.modelRing t ht hd model M cache).decode _ = _ at hs
  simp only [RingProgram.modelRing_program] at hs
  change rawDenote (RingProgram.denote (RingProgram.scalarRing 3 t M cache)
    (LiftRing.of (model.F t)) (RingBasis.basis (model.F t))) _ = _ at hs
  rw [hs, dense_eval_canonical]

end


/-- The byte ABI of the native incidence emitter is the product dictionary ABI. -/
theorem dictionaryBits_productBytes {n B d : ℕ} (source : List (Product.Entry n B d)) :
    PerturbationProgram.dictionaryBits source = Product.bytes source := by
  induction source with
  | nil => rfl
  | cons a source ih =>
    simpa only [PerturbationProgram.dictionaryBits_cons, Product.bytes, Normalize.bytes,
      Squarefree.Program.encodeDictionary, List.map_cons, Squarefree.Program.rawEntries] using
      congrArg (fun bits => Encoding.frame (Squarefree.encodeIndex a.1) ++
        Encoding.frame (RingProgram.flat a.2) ++ bits) ih

def emittedSource (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool)) :
    List (Product.Entry rows.length (baseWidth 3 t) d) :=
  PerturbationAssembly.outputWords (RingProgram.modelProgram t model M cache) J theta
    (PerturbationBetaProgram.runValue t model M cache theta (PerturbationAssembly.pairedRows rows))
    (fun v : Fin rows.length => rows[v].1.val)

theorem lowOutput_productBytes (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool)) :
    PerturbationAssembly.lowOutput t model M cache J N theta rows [] =
      Product.bytes (emittedSource t model M cache J N theta rows) := by
  rw [PerturbationAssembly.lowOutput_dictionary, dictionaryBits_productBytes]
  rfl

/-- Uniform scalar envelope for the actual shifted-row work. -/
theorem rowWork_polynomial (N J n d B A : ℕ)
    (hN : N ≤ A) (hJ : J ≤ A) (hn : n ≤ A) (hd : d ≤ A) (hB : B ≤ A)
    (ha : 1 ≤ A) : PerturbationAssembly.rowWorkPolynomial N J n d B ≤ 100000000 * A ^ 9 := by
  have hm : PerturbationAssembly.rowWorkPolynomial N J n d B ≤ PerturbationAssembly.rowWorkPolynomial A A A A A := by
    unfold PerturbationAssembly.rowWorkPolynomial DensePolynomialProgram.AddService.budget
    gcongr
  have h0 : 1 ≤ A ^ 9 := Nat.one_le_pow 9 A ha
  have h1 : A ≤ A ^ 9 := by simpa using pow_le_pow_right' ha (show 1 ≤ 9 by decide)
  have h2 : A ^ 2 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h3 : A ^ 3 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h4 : A ^ 4 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h5 : A ^ 5 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h6 : A ^ 6 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h7 : A ^ 7 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  have h8 : A ^ 8 ≤ A ^ 9 := pow_le_pow_right' ha (by decide)
  apply hm.trans
  unfold PerturbationAssembly.rowWorkPolynomial DensePolynomialProgram.AddService.budget
  ring_nf
  omega


/-- The actual low emitter has a fixed tenth-degree budget in its concrete
row count, dense row length, truncation length, ring word widths and cache sizes. -/
theorem lowWork_polynomial (n N J t d E : ℕ) :
    PerturbationAssembly.lowWorkPolynomial n N J t d E ≤
      1000000000 * (n + N + J + d + baseWidth 3 t + E + 1) ^ 10 := by
  let B := baseWidth 3 t
  let A := n + N + J + d + B + E + 1
  have ha : 1 ≤ A := by dsimp [A]; omega
  have hn : n ≤ A := by dsimp [A]; omega
  have hN : N ≤ A := by dsimp [A]; omega
  have hJ : J ≤ A := by dsimp [A]; omega
  have hd : d ≤ A := by dsimp [A]; omega
  have hB : B ≤ A := by dsimp [A]; omega
  have hE : E ≤ A := by dsimp [A]; omega
  have hrow := rowWork_polynomial N J n d B A hN hJ hn hd hB ha
  have hm : PerturbationAssembly.lowWorkPolynomial n N J t d E ≤
      1000000*(A+1)*(A+1)*(A+1)^3*(A+1)^2 + (33*A+20*(A*A)+83) +
      (9*A+14*A+9*(A*(A*A))+7*(A*A)+440*(A+1)*(A*A+1)+47) +
      (7*(A*(2*(A*(A*A))+2)+1)+9*A+A*(100000000*A^9+2)+20) +
      (2*(2*(A*(A*A))+2*A+A*A)+6*A+33) + (2*(A*A)+3) := by
    unfold PerturbationAssembly.lowWorkPolynomial
    change 1000000*(n+1)*(N+1)*(d+1)^3*(B+1)^2 + (33*n+20*(d*B)+83) +
      (9*E+14*J+9*(J*(d*B))+7*(d*B)+440*(J+1)*(d*B+1)+47) +
      (7*(n*(2*(N*(d*B))+2)+1)+9*n+n*(PerturbationAssembly.rowWorkPolynomial N J n d B+2)+20) +
      (2*(2*(J*(d*B))+2*J+d*B)+6*E+33) + (2*(d*B)+3) ≤ _
    gcongr
  have h0 : 1 ≤ A ^ 10 := Nat.one_le_pow 10 A ha
  have h1 : A ≤ A ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : A ^ 2 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : A ^ 3 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : A ^ 4 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h5 : A ^ 5 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h6 : A ^ 6 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h7 : A ^ 7 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  change PerturbationAssembly.lowWorkPolynomial n N J t d E ≤ 1000000000 * A ^ 10
  apply hm.trans
  ring_nf
  omega


/-- The fixed native emitter actually computes beta and all singleton records;
all source prefixes are charged before the immediate correction substitution. -/
theorem low_run_space (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (low : SubexpConvolutionControl.Store)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (regs : Fin 16 → Bool) :
    let source := emittedSource t model M cache J N theta rows
    let bound := PerturbationAssembly.lowWorkPolynomial rows.length N J t d
      ((low 192).length + (low 193).length + (low 243).length) + 1
    ∃ steps rr, steps ≤ bound ∧
      Trace lowProgram steps
        ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry))
        ((⟨rr, Function.update low 217 (Product.bytes source)⟩ : State 16 256).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace lowProgram prefixSteps
          ((⟨regs, low⟩ : State 16 256).withPC (some lowProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits low + bound := by
  dsimp only
  obtain ⟨steps, rr, hb, he⟩ := hinput.run_polynomial regs
  rw [hout, lowOutput_productBytes] at he
  have ht := compiled_halt_trace he 205 217
  refine ⟨steps + 1, rr, by omega, ht, ?_⟩
  intro prefixSteps intermediate hp htrace i
  exact StructuredSpace.local_stack_bound lowProgram
    (steps := PerturbationAssembly.lowWorkPolynomial rows.length N J t d
      ((low 192).length + (low 193).length + (low 243).length) + 1)
    (by rfl) prefixSteps intermediate (by omega) htrace i

namespace Native

open SubexpScanPrimitives SubexpSetupStorage

theorem loadPairs_valid : ∀ p ∈ loadPairs,
    p.1 ≠ p.2 ∧ p.1 ≠ 292 ∧ (292 : Fin 294) ≠ p.2 := by
  intro p hp
  simp only [loadPairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem load_eval (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool) :
    Eval loadCommand (7 * ((low 194).length + (low 202).length + (low 204).length) +
      6 * (low 217).length + 21)
      (joinedState regs low (emptyHigh mask)) (loaded (joinedState regs low (emptyHigh mask))) := by
  let a := joinedState regs low (emptyHigh mask)
  let b := copyManyState loadPairs a
  let c := afterTransfer b 217 292 0 1
  have hcopy := copyMany_eval 292 loadPairs a loadPairs_valid (by rfl)
  have hfirst := SubexpScanPrimitives.transfer_eval b 217 292 0 1 (by decide) (by decide)
  have hsecond := SubexpScanPrimitives.transfer_eval c 292 284 0 1 (by decide) (by decide)
  have he := hcopy.seq (hfirst.seq hsecond)
  unfold loadCommand loaded
  convert he using 1
  change 7 * ((low 194).length + (low 202).length + (low 204).length) +
      6 * (low 217).length + 21 =
    (7 * (low 194).length + 5 + (7 * (low 202).length + 5 +
      (7 * (low 204).length + 5 + 0))) +
      (3 * (low 217).length + 3 + (3 * ((low 217).reverse ++ []).length + 3))
  simp only [List.length_append, List.length_reverse, List.length_nil]
  omega

theorem loaded_high (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool)
    (i : Fin 38) :
    (loaded (joinedState regs low (emptyHigh mask))).stacks (producerPorts i) =
      (state (fun _ => false) (low 194) (low 202) (low 204) [] []
        {input := low 217, target := mask}).stacks i := by
  fin_cases i <;> first
    | rfl
    | (change low 194 ++ [] = low 194; exact List.append_nil _)
    | (change low 202 ++ [] = low 202; exact List.append_nil _)
    | (change low 204 ++ [] = low 204; exact List.append_nil _)
    | (change ((low 217).reverse ++ []).reverse ++ [] = low 217; simp)

theorem loaded_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool)
    (i : Fin 256) :
    (loaded (joinedState regs low (emptyHigh mask))).stacks (lowPorts i) =
      (Function.update low 217 []) i := by
  have hi : (lowPorts i).val < 256 := i.isLt
  have h261 : lowPorts i ≠ 261 := by intro h; have := congrArg Fin.val h; omega
  have h268 : lowPorts i ≠ 268 := by intro h; have := congrArg Fin.val h; omega
  have h280 : lowPorts i ≠ 280 := by intro h; have := congrArg Fin.val h; omega
  have h284 : lowPorts i ≠ 284 := by intro h; have := congrArg Fin.val h; omega
  have h292 : lowPorts i ≠ 292 := by intro h; have := congrArg Fin.val h; omega
  by_cases h217 : i = 217
  · subst i
    rfl
  · have h217' : lowPorts i ≠ 217 := by
      intro h
      apply h217
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [lowPorts] using hv
    simp [loaded, loadPairs, copyManyState, copyState, afterTransfer,
      StackRoutines.copyStacks, StackRoutines.transferStacks,
      h261, h268, h280, h284, h292, h217', h217]

theorem embed_low (regs rr : Fin 16 → Bool) (low low' : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) :
    embedState id lowPorts (joinedState regs low high) ⟨rr, low'⟩ = joinedState rr low' high := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id lowPorts_injective
  · intro i; rfl
  · intro i; simp [joinedState, lowPorts]
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i hi
    have hge : 256 ≤ i.val := by
      by_contra h
      apply hi
      exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    let j : Fin 38 := ⟨i.val - 256, by omega⟩
    have hj : producerPorts j = i := by
      apply Fin.ext
      simp only [producerPorts, Fin.val_natAdd, j]
      omega
    rw [← hj]
    simp [joinedState, producerPorts]


theorem embed_loaded (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool) :
    let a := loaded (joinedState regs low (emptyHigh mask))
    embedState producerRegisters producerPorts a
      (state (a.regs ∘ producerRegisters) (low 194) (low 202) (low 204) [] []
        {input := low 217, target := mask}) = a := by
  dsimp only
  apply SubexpScanPrimitives.embedState_eq _ _ producerRegisters_injective producerPorts_injective
  · intro i; rfl
  · exact loaded_high regs low mask
  · intro i hi; rfl
  · intro i hi; rfl

theorem highPorts_mem (i : Fin 294) : i ∈ highPorts ↔ 256 ≤ i.val := by
  simp only [highPorts, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    simp [producerPorts]
  · intro hi
    refine ⟨⟨i.val - 256, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [producerPorts, Fin.val_natAdd]
    omega

theorem finish_eval (a : State 16 294) (hscratch : a.stacks 292 = []) :
    Eval finishCommand (6 * (a.stacks 271).length + 6 + clearManyCost highPorts (movedOutput a))
      a (finished a) := by
  have h1 := SubexpScanPrimitives.transfer_eval a 271 292 0 1 (by decide) (by decide)
  have h2 := SubexpScanPrimitives.transfer_eval (afterTransfer a 271 292 0 1)
    292 217 0 1 (by decide) (by decide)
  have ho : Eval outputMove (6 * (a.stacks 271).length + 6) a (movedOutput a) := by
    unfold outputMove movedOutput
    convert h1.seq h2 using 1
    simp [afterTransfer, StackRoutines.transferStacks, hscratch]
    omega
  exact ho.seq (clearMany_eval highPorts (movedOutput a))

theorem finished_high (a : State 16 294) (i : Fin 38) :
    (finished a).stacks (producerPorts i) = [] := by
  rw [finished, clearMany_stacks, ite_eq_left]
  exact (highPorts_mem _).mpr (by simp [producerPorts])

theorem finished_low (a : State 16 294) (hscratch : a.stacks 292 = [])
    (hempty : a.stacks 217 = []) (i : Fin 256) :
    (finished a).stacks (lowPorts i) =
      (Function.update (fun j => a.stacks (lowPorts j)) 217 (a.stacks 271)) i := by
  have hi : (lowPorts i).val < 256 := i.isLt
  rw [finished, clearMany_stacks, ite_eq_right ((highPorts_mem _).not.mpr (by omega))]
  have h271 : lowPorts i ≠ 271 := by intro h; have := congrArg Fin.val h; omega
  have h292 : lowPorts i ≠ 292 := by intro h; have := congrArg Fin.val h; omega
  by_cases h217 : i = 217
  · subst i
    simp [movedOutput, afterTransfer, StackRoutines.transferStacks, lowPorts, hscratch, hempty]
  · have h217' : lowPorts i ≠ 217 := by
      intro h
      apply h217
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [lowPorts] using hv
    simp [movedOutput, afterTransfer, StackRoutines.transferStacks,
      h271, h292, h217', h217]


theorem emptyHigh_nil (i : Fin 38) : emptyHigh [] i = [] := by
  fin_cases i <;> rfl

theorem embed_producer_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) (out : State 8 38) (i : Fin 256) :
    (embedState producerRegisters producerPorts
      (loaded (joinedState regs low (emptyHigh mask))) out).stacks (lowPorts i) =
        (Function.update low 217 []) i := by
  rw [embedState_stack_frame _ _ _ _ _]
  · exact loaded_low regs low mask i
  · rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    have hi := i.isLt
    simp only [producerPorts, lowPorts, Fin.val_natAdd, Fin.val_castAdd] at hv
    omega

theorem finished_producer_shape (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) (rr : Fin 8 → Bool) (modulus width degree bits : List Bool) :
    let out := state rr modulus width degree bits [] {target := mask.reverse}
    let embedded := embedState producerRegisters producerPorts
      (loaded (joinedState regs low (emptyHigh mask))) out
    finished embedded = joinedState (finished embedded).regs
      (Function.update low 217 bits) (emptyHigh []) := by
  dsimp only
  let out := state rr modulus width degree bits [] {target := mask.reverse}
  let embedded := embedState producerRegisters producerPorts
    (loaded (joinedState regs low (emptyHigh mask))) out
  have hscratch : embedded.stacks 292 = [] := by
    change embedded.stacks (producerPorts 36) = []
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  have hempty : embedded.stacks 217 = [] := by
    change embedded.stacks (lowPorts 217) = []
    rw [embed_producer_low]
    rfl
  have hword : embedded.stacks 271 = bits := by
    change embedded.stacks (producerPorts 15) = bits
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    by_cases hi : i.val < 256
    · let j : Fin 256 := ⟨i.val, hi⟩
      have hj : lowPorts j = i := Fin.ext rfl
      rw [← hj, joinedState_low]
      change (finished embedded).stacks (lowPorts j) = (Function.update low 217 bits) j
      rw [finished_low embedded hscratch hempty j, hword]
      have hh : (fun k => embedded.stacks (lowPorts k)) = Function.update low 217 [] := by
        funext k
        exact embed_producer_low regs low mask out k
      rw [hh, Function.update_idem]
    · let j : Fin 38 := ⟨i.val - 256, by omega⟩
      have hj : producerPorts j = i := by
        apply Fin.ext
        simp only [producerPorts, Fin.val_natAdd, j]
        omega
      rw [← hj, joinedState_high]
      change (finished embedded).stacks (producerPorts j) = emptyHigh [] j
      rw [finished_high, emptyHigh_nil]


theorem clearManyCost_le_on (ps : List (Fin 294)) (a : State 16 294) (B : ℕ)
    (ha : ∀ i ∈ ps, (a.stacks i).length ≤ B) :
    clearManyCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
    have hb : ∀ i ∈ ps, ((clearState p a).stacks i).length ≤ B := by
      intro i hi
      by_cases h : i = p
      · subst i; simp [clearState]
      · simpa [clearState, h] using ha i (by simp [hi])
    have hc := ih (clearState p a) hb
    have hp := ha p (by simp)
    simp only [clearManyCost, List.length_cons]
    nlinarith

theorem core_words_le (regs : Fin 8 → Bool) (modulus width degree bits mask : List Bool)
    (B : ℕ) (hm : modulus.length ≤ B) (hw : width.length ≤ B) (hd : degree.length ≤ B)
    (ho : bits.length ≤ B) (hmask : mask.length ≤ B) (i : Fin 38) :
    ((state regs modulus width degree bits [] {target := mask}).stacks i).length ≤ B := by
  fin_cases i <;> first | exact hm | exact hw | exact hd | exact ho | exact hmask | exact Nat.zero_le _

theorem finish_cost_le (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) (rr : Fin 8 → Bool) (modulus width degree bits : List Bool) :
    let out := state rr modulus width degree bits [] {target := mask.reverse}
    let embedded := embedState producerRegisters producerPorts
      (loaded (joinedState regs low (emptyHigh mask))) out
    clearManyCost highPorts (movedOutput embedded) ≤
      38 * (2 * (modulus.length + width.length + degree.length + mask.length + bits.length) + 3) := by
  dsimp only
  let out := state rr modulus width degree bits [] {target := mask.reverse}
  let a := embedState producerRegisters producerPorts
    (loaded (joinedState regs low (emptyHigh mask))) out
  have hbound := clearManyCost_le_on highPorts (movedOutput a)
    (modulus.length + width.length + degree.length + mask.length + bits.length)
  simp only [highPorts, List.length_map, List.length_finRange] at hbound
  apply hbound
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  have h217 : producerPorts j ≠ 217 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [producerPorts, Fin.val_natAdd] at hv
    omega
  by_cases h271 : producerPorts j = 271
  · simp [movedOutput, afterTransfer, StackRoutines.transferStacks, h271]
  by_cases h292 : producerPorts j = 292
  · simp [movedOutput, afterTransfer, StackRoutines.transferStacks, h292]
  simp only [movedOutput, afterTransfer, StackRoutines.transferStacks, Function.update_apply,
    ite_eq_right h217, ite_eq_right h292, ite_eq_right h271]
  rw [embedState_stack _ _ _ _ producerPorts_injective]
  exact core_words_le rr modulus width degree bits mask.reverse _
    (by omega) (by omega) (by omega) (by omega) (by simp; omega) j

def combinedBudget (lowWork cacheLength rawLength n B d u J count : ℕ) : ℕ :=
  let outputLength := u * J * (2 * (u + J + n) + 2 * (d * B) + 2)
  lowWork + 1 + (7 * cacheLength + 6 * rawLength + 21) +
    (preparedBudget n B d u J count rawLength +
      (6 * outputLength + 6 + 38 * (2 * (cacheLength + n + outputLength) + 3))) + 1



/-- The full local join retains a fixed polynomial degree, including cleanup. -/
theorem combinedBudget_polynomial (lowWork cacheLength rawLength n B d u J count : ℕ) :
    combinedBudget lowWork cacheLength rawLength n B d u J count ≤
      3200000 * (lowWork + cacheLength + rawLength + n + B + d + u + J + count + 1) ^ 10 := by
  let a := lowWork + cacheLength + rawLength + n + B + d + u + J + count + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hl : lowWork ≤ a := by dsimp [a]; omega
  have hc : cacheLength ≤ a := by dsimp [a]; omega
  have hr : rawLength ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hB : B ≤ a := by dsimp [a]; omega
  have hd : d ≤ a := by dsimp [a]; omega
  have hu : u ≤ a := by dsimp [a]; omega
  have hJ : J ≤ a := by dsimp [a]; omega
  have hp := preparedBudget_polynomial n B d u J count rawLength
  have hsum : n + B + d + u + J + count + rawLength + 1 ≤ a := by dsimp [a]; omega
  have hp' : preparedBudget n B d u J count rawLength ≤ 3100000 * a ^ 10 :=
    hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 10))
  have ho : u * J * (2 * (u + J + n) + 2 * (d * B) + 2) ≤
      a * a * (2 * (a + a + a) + 2 * (a * a) + 2) := by gcongr
  have he : a * a * (2 * (a + a + a) + 2 * (a * a) + 2) =
      2 * a ^ 4 + 6 * a ^ 3 + 2 * a ^ 2 := by ring
  rw [he] at ho
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  change combinedBudget lowWork cacheLength rawLength n B d u J count ≤ 3200000 * a ^ 10
  dsimp only [combinedBudget]
  omega

/-- Substituting the actual emitter work preserves one fixed polynomial
exponent for the complete local source-to-specialized-dictionary join. -/
theorem combinedBudget_lowWork_polynomial (n N J t d E cacheLength rawLength u count : ℕ) :
    combinedBudget (PerturbationAssembly.lowWorkPolynomial n N J t d E)
      cacheLength rawLength n (baseWidth 3 t) d u J count ≤
      (3200000 * 1000000001 ^ 10) *
        (n + N + J + d + baseWidth 3 t + E + cacheLength + rawLength + u + count + 1) ^ 100 := by
  let A := n + N + J + d + baseWidth 3 t + E + cacheLength + rawLength + u + count + 1
  have ha : 1 ≤ A := by dsimp [A]; omega
  have hbase : n + N + J + d + baseWidth 3 t + E + 1 ≤ A := by dsimp [A]; omega
  have hw := (lowWork_polynomial n N J t d E).trans
    (Nat.mul_le_mul_left 1000000000 (Nat.pow_le_pow_left hbase 10))
  have ha10 : A ≤ A ^ 10 := by
    simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have hrest : cacheLength + rawLength + n + baseWidth 3 t + d + u + J + count + 1 ≤ A := by
    dsimp [A]; omega
  have hsum : PerturbationAssembly.lowWorkPolynomial n N J t d E +
      cacheLength + rawLength + n + baseWidth 3 t + d + u + J + count + 1 ≤
        1000000001 * A ^ 10 := by omega
  have hp := combinedBudget_polynomial
    (PerturbationAssembly.lowWorkPolynomial n N J t d E)
    cacheLength rawLength n (baseWidth 3 t) d u J count
  apply hp.trans
  change 3200000 * _ ^ 10 ≤ (3200000 * 1000000001 ^ 10) * A ^ 100
  calc
    _ ≤ 3200000 * (1000000001 * A ^ 10) ^ 10 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 10)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]

/-- Substituting the proved origin/singleton byte bound removes the raw
record count and raw byte length from the polynomial's input dimensions. -/
theorem combinedBudget_incidence_polynomial
    (n N J t d E cacheLength rawLength u : ℕ)
    (hraw : rawLength ≤ (1 + n * (J - 1)) *
      (2 * (u + J + n) + 2 * (d * baseWidth 3 t) + 2)) :
    combinedBudget (PerturbationAssembly.lowWorkPolynomial n N J t d E)
      cacheLength rawLength n (baseWidth 3 t) d u J (1 + n * (J - 1)) ≤
      (3200000 * 1000000023 ^ 10) *
        (n + N + J + d + baseWidth 3 t + E + cacheLength + u + 1) ^ 100 := by
  let B := baseWidth 3 t
  let A := n + N + J + d + B + E + cacheLength + u + 1
  have ha : 1 ≤ A := by dsimp [A]; omega
  have hn : n ≤ A := by dsimp [A]; omega
  have hJ : J ≤ A := by dsimp [A]; omega
  have hd : d ≤ A := by dsimp [A]; omega
  have hB : B ≤ A := by dsimp [A]; omega
  have hu : u ≤ A := by dsimp [A]; omega
  have hc : 1 + n * (J - 1) ≤ 1 + A * A := by gcongr; exact (Nat.sub_le J 1).trans hJ
  have hr : rawLength ≤ (1 + A * A) * (2 * (A + A + A) + 2 * (A * A) + 2) := by
    apply hraw.trans
    gcongr
  have h04 : 1 ≤ A ^ 4 := Nat.one_le_pow 4 A ha
  have h14 : A ≤ A ^ 4 := by simpa using pow_le_pow_right' ha (show 1 ≤ 4 by decide)
  have h24 : A ^ 2 ≤ A ^ 4 := pow_le_pow_right' ha (by decide)
  have h34 : A ^ 3 ≤ A ^ 4 := pow_le_pow_right' ha (by decide)
  have hr' : rawLength ≤ 20 * A ^ 4 := by
    ring_nf at hr
    omega
  have hbase : n + N + J + d + baseWidth 3 t + E + 1 ≤ A := by dsimp [A, B]; omega
  have hw := (lowWork_polynomial n N J t d E).trans
    (Nat.mul_le_mul_left 1000000000 (Nat.pow_le_pow_left hbase 10))
  have h010 : 1 ≤ A ^ 10 := Nat.one_le_pow 10 A ha
  have h110 : A ≤ A ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h210 : A ^ 2 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have h410 : A ^ 4 ≤ A ^ 10 := pow_le_pow_right' ha (by decide)
  have hrest : cacheLength + n + baseWidth 3 t + d + u + J + 1 ≤ A := by
    dsimp [A, B]; omega
  have hsum : PerturbationAssembly.lowWorkPolynomial n N J t d E +
      cacheLength + rawLength + n + baseWidth 3 t + d + u + J + (1 + n * (J - 1)) + 1 ≤
        1000000023 * A ^ 10 := by
    rw [← pow_two] at hc
    omega
  have hp := combinedBudget_polynomial
    (PerturbationAssembly.lowWorkPolynomial n N J t d E)
    cacheLength rawLength n (baseWidth 3 t) d u J (1 + n * (J - 1))
  apply hp.trans
  change 3200000 * _ ^ 10 ≤ (3200000 * 1000000023 ^ 10) * A ^ 100
  calc
    _ ≤ 3200000 * (1000000023 * A ^ 10) ^ 10 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 10)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]

/-- The original native emitter, immediate correction substitution, additive
normalization and cleanup execute on one fixed source machine. Every incoming
word assertion describes the concrete scalar caches or row serialization. -/
theorem run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (low : SubexpConvolutionControl.Store)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (regs : Fin 16 → Bool) (U : Finset (Fin rows.length)) :
    let source := emittedSource t model M cache J N theta rows
    let result := Normalize.run 3 t M cache (HeadEvaluation.specializeEntries U source) []
    let start := joinedState regs low (emptyHigh (Squarefree.encodeMask U))
    let bound := combinedBudget
      (PerturbationAssembly.lowWorkPolynomial rows.length N J t d
        ((low 192).length + (low 193).length + (low 243).length))
      ((low 194).length + (low 202).length + (low 204).length)
      (Product.bytes source).length rows.length (baseWidth 3 t) d u J (1 + rows.length * (J - 1))
    ∃ steps rr, steps ≤ bound ∧
      Trace program steps (start.withPC (some program.entry))
        ((joinedState rr (Function.update low 217 (Product.bytes result)) (emptyHigh [])).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (start.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks + bound := by
  dsimp only
  let source := emittedSource t model M cache J N theta rows
  let result := Normalize.run 3 t M cache (HeadEvaluation.specializeEntries U source) []
  let mask := Squarefree.encodeMask U
  let emitted := Function.update low 217 (Product.bytes source)
  have hvalid : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1 :=
    incidence_valid (RingProgram.modelRing t ht hd model M cache) u J hu hJ theta _ _
  have hlength : source.length ≤ 1 + rows.length * (J - 1) := by
    exact le_of_eq (incidence_entries_length _ J theta _ _)
  obtain ⟨lowSteps, lowRegs, hlowSteps, hlow, _⟩ :=
    low_run_space t model M cache J N theta rows low hinput hout regs
  have hlowCall := eval_call_lifted lowProgram id lowPorts
    (joinedState regs low (emptyHigh mask)) Function.injective_id lowPorts_injective hlow
  rw [embed_low, embed_low] at hlowCall
  have hload := load_eval lowRegs emitted mask
  let loadedState := loaded (joinedState lowRegs emitted (emptyHigh mask))
  let coreRegs := loadedState.regs ∘ producerRegisters
  obtain ⟨coreSteps, rr, hcoreSteps, hcore, hgood, _⟩ :=
    prepared_run_space 3 t M cache U source hvalid hlength coreRegs (low 202) (low 204)
      hinput.scalarReady.degree hinput.scalarReady.width
  have hcoreCall := eval_call_lifted preparedProgram producerRegisters producerPorts
    loadedState producerRegisters_injective producerPorts_injective hcore
  have hstart : embedState producerRegisters producerPorts loadedState
      (state coreRegs M.bits (low 202) (low 204) [] []
        {input := Product.bytes source, target := mask}) = loadedState := by
    simpa only [emitted, Function.update_of_ne (by decide : (194 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (202 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (204 : Fin 256) ≠ 217), Function.update_self,
      hinput.scalarReady.modulus] using embed_loaded lowRegs emitted mask
  rw [hstart] at hcoreCall
  let coreOut := state rr M.bits (low 202) (low 204) (Product.bytes result) []
    {target := mask.reverse}
  let finalCore := embedState producerRegisters producerPorts loadedState coreOut
  have hscratch : finalCore.stacks 292 = [] := by
    change finalCore.stacks (producerPorts 36) = []
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  have hword : finalCore.stacks 271 = Product.bytes result := by
    change finalCore.stacks (producerPorts 15) = Product.bytes result
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  have hfinish := finish_eval finalCore hscratch
  have hfinished : finished finalCore = joinedState (finished finalCore).regs
      (Function.update low 217 (Product.bytes result)) (emptyHigh []) := by
    simpa only [emitted, Function.update_idem] using
      finished_producer_shape lowRegs emitted mask rr M.bits (low 202) (low 204) (Product.bytes result)
  rw [hfinished] at hfinish
  have he := hlowCall.seq (hload.seq (hcoreCall.seq hfinish))
  have houtput := TruncatedRingProgram.empty_bytes_length_le hgood
  change (Product.bytes result).length ≤ _ at houtput
  have hclear := finish_cost_le lowRegs emitted mask rr M.bits (low 202) (low 204)
    (Product.bytes result)
  have hbound : lowSteps +
      (7 * ((emitted 194).length + (emitted 202).length + (emitted 204).length) +
        6 * (emitted 217).length + 21 +
        (coreSteps + (6 * (finalCore.stacks 271).length + 6 +
          clearManyCost highPorts (movedOutput finalCore)))) + 1 ≤
      combinedBudget
        (PerturbationAssembly.lowWorkPolynomial rows.length N J t d
          ((low 192).length + (low 193).length + (low 243).length))
        ((low 194).length + (low 202).length + (low 204).length)
        (Product.bytes source).length rows.length (baseWidth 3 t) d u J (1 + rows.length * (J - 1)) := by
    have hmask : mask.length = rows.length := Squarefree.encodeMask_length U
    have hmod : M.bits.length = (low 194).length := congrArg List.length hinput.scalarReady.modulus.symm
    simp only [emitted, Function.update_of_ne (by decide : (194 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (202 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (204 : Fin 256) ≠ 217), Function.update_self, hword]
    dsimp only [combinedBudget]
    change clearManyCost highPorts (movedOutput finalCore) ≤ _ at hclear
    rw [hmask, hmod] at hclear
    omega
  refine ⟨_, (finished finalCore).regs, hbound, ?_, hgood, ?_⟩
  · exact compiled_halt_trace he 205 217
  · intro prefixSteps intermediate hp htrace i
    exact StructuredSpace.local_stack_bound program (by rfl) prefixSteps intermediate
      (hp.trans hbound) htrace i

end Native

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
