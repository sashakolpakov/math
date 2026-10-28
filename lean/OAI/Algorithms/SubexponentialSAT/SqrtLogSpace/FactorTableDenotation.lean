import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTablePayloadMeaning
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCacheProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorInput
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblySourceStored

/-! The actual normalized incidence payload has the canonical scalarized
source denotation. Source arrays are witnesses produced by the finite source
machine; their full polynomial meanings identify one fixed incidence jet. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

theorem product_bytes_injective {n B d : ℕ} (hB : 0 < B) :
    Function.Injective (Product.bytes : List (Product.Entry n B d) → List Bool) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hl := congrArg List.length h
          simp [Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary,
            Squarefree.Program.rawEntries] at hl
          omega
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hl := congrArg List.length h
          simp [Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary,
            Squarefree.Program.rawEntries] at hl
      | cons y ys =>
          change (Encoding.frame (Squarefree.encodeIndex x.1) ++
            Encoding.frame (RingProgram.flat x.2)) ++ Product.bytes xs =
            (Encoding.frame (Squarefree.encodeIndex y.1) ++
            Encoding.frame (RingProgram.flat y.2)) ++ Product.bytes ys at h
          rw [List.append_assoc, List.append_assoc] at h
          obtain ⟨hk, ht⟩ := Encoding.frame_append_injective h
          obtain ⟨hc, ht⟩ := Encoding.frame_append_injective ht
          exact congrArg₂ List.cons (Prod.ext (Squarefree.encodeIndex_injective hk)
            (RingProgram.flat_injective hB hc)) (ih ht)

theorem normalized_specialization_raw (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (U : Finset (Fin n)) (source : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawDenote f (Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []) =
      Moments.jetScalar (Moments.jetEval (fun v => if v ∈ U then (1 : R) else 0)
        (by intro v; split <;> simp) (rawDenote f source)) := by
  dsimp only
  rw [normalize_denote p t M cache scalar basis _ [] (by simp [Squarefree.Sparse.keys])]
  have hz : rawDenote (n := n)
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) [] = 0 := by
    simp [rawDenote, Dictionary.denoteTable, Squarefree.Sparse.denote, Squarefree.Sparse.decode]
  rw [hz, add_zero, QueryProducerSpace.specialized_raw_denote]

/-- The exact correction word is interpreted on the declared ambient type. -/
def specializedJet {n : ℕ} (u J : ℕ) (mask : List Bool)
    (jet : Squarefree.Jet (Fin n) R) : Squarefree.Jet (Fin n) R :=
  Squarefree.canonical u J (Moments.jetScalar (Moments.jetEval
    (fun v => if v ∈ Squarefree.decodeMask n mask then (1 : R) else 0)
    (by intro v; split <;> simp) jet))

theorem specializedJet_atom_origin {n : ℕ} (u J : ℕ) (mask : List Bool) (c : R) :
    specializedJet (n := n) u J mask (Squarefree.Sparse.atom Squarefree.Index.origin c) =
      Squarefree.canonical u J (Squarefree.Sparse.atom Squarefree.Index.origin c) := by
  unfold specializedJet
  rw [HeadEvaluation.specialize_atom]
  simp [Squarefree.Index.origin]
theorem rawDenote_constant {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) (c : RingProgram.Code (Word B) d) :
    rawDenote (n := n) f (Squarefree.Sparse.constant u J c) =
      Squarefree.canonical u J (Squarefree.Sparse.atom Squarefree.Index.origin (f c)) := by
  have hm : Dictionary.denoteTable f (Squarefree.Sparse.constant (V := Fin n) u J c) =
      Squarefree.Sparse.constant u J (f c) := by
    by_cases h : 0 < u ∧ 0 < J <;>
      simp [Squarefree.Sparse.constant, h, Dictionary.denoteTable]
  change Squarefree.Sparse.denote _ = _
  rw [hm, Squarefree.Sparse.denote_constant]

theorem oneEntries_rawDenote {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (one : RingProgram.Code (Word B) d)
    (hone : f one = 1) :
    rawDenote f (FactorAssignmentProgram.oneEntries (n := n) one) = 1 := by
  simp [FactorAssignmentProgram.oneEntries, rawDenote, Dictionary.denoteTable,
    Squarefree.Sparse.denote, Squarefree.Sparse.decode, hone]

/-- The actual singleton identity is neutral even when one cutoff is zero. -/
theorem oneEntries_rawValue {n B d : ℕ} (u J : ℕ)
    (f : RingProgram.Code (Word B) d → R) (one : RingProgram.Code (Word B) d)
    (hone : f one = 1) :
    rawValue u J f (FactorAssignmentProgram.oneEntries (n := n) one) = 1 := by
  rw [rawValue, oneEntries_rawDenote f one hone, map_one]


/-- The raw identity also determines the bounded dense readout without any
injectivity assumption about coefficient encodings. -/
theorem rawValue_of_specialized {n B d : ℕ} (u J : ℕ) (mask : List Bool)
    (f : RingProgram.Code (Word B) d → R) (entries : List (Product.Entry n B d))
    (jet : Squarefree.Jet (Fin n) R)
    (h : rawDenote f entries = specializedJet u J mask jet) :
    rawValue u J f entries = Dense.ofPolynomial u J (Moments.jetEval
      (fun v => if v ∈ Squarefree.decodeMask n mask then (1 : R) else 0)
      (by intro v; split <;> simp) jet) := by
  rw [rawValue, h, specializedJet, jetProjection_canonical, jetProjection_jetScalar]

/-- Normalization and dimension transport retain the exact canonical raw
identity; the native source theorem instantiates its source equality below. -/
theorem specialized_source_realizes (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {m n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (u J : ℕ) (mask : List Bool) (source : List (Product.Entry m (baseWidth p t) d))
    (hn : m = n) (hvalid : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
    (jet : Squarefree.Jet (Fin n) R)
    (hsource : PerturbationAssembly.castJet hn
      (rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) source) =
        Squarefree.canonical u J jet) :
    ∃ entries : List (Product.Entry n (baseWidth p t) d),
      Product.bytes (Normalize.run p t M cache
        (HeadEvaluation.specializeEntries (Squarefree.decodeMask m mask) source) []) =
          Product.bytes entries ∧ Good ∅ u J entries ∧
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) entries =
        specializedJet u J mask jet := by
  cases hn
  refine ⟨_, rfl, normalize_good p t M cache ∅ u J _ []
    (QueryProducerSpace.specialized_valid _ source hvalid) Good.nil, ?_⟩
  rw [normalized_specialization_raw]
  change rawDenote _ source = Squarefree.canonical u J jet at hsource
  rw [hsource]
  have hh := QueryJetSemantics.jetScalar_eval_canonical (W := Fin m) u J
    (fun v => decide (v ∈ Squarefree.decodeMask m mask)) jet
  have hf : Squarefree.boolValue (R := R) (fun v => decide (v ∈ Squarefree.decodeMask m mask)) =
      (fun v => if v ∈ Squarefree.decodeMask m mask then (1 : R) else 0) := by
    funext v
    simp [Squarefree.boolValue]
  simpa only [specializedJet, hf] using hh

/-- The fixed source incidence is independent of the source call's array witness. -/
def fixedLowJet {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (choice : List Bool) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  Moments.incidenceJet (PerturbationAssembly.fixedSourceRow p ps P n f j)
    (p.ops.decode theta)
    (∑ v : Fin n, (PerturbationAssembly.fixedSourceRow p ps P n f j v).eval
      (p.ops.decode theta) * (if choice.getD v.val false then 1 else 0))

/-- The actual additive normalizer returns an empty-support dictionary whose
whole raw denotation is the intended specialized incidence, at both cutoffs. -/
theorem low_payload_realizes {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R + 1)))
    (hx : xs.length = n) (choice mask : List Bool) (hc : choice.length = n)
    (hs : PerturbationAssembly.sourceRowProperty p ps P n f j xs) :
    ∃ entries : List (Product.Entry n (baseWidth 3 p.t) d),
      FactorTableNative.specializedRowPayload p.t p.model p.modulus p.cache J (p.R + 1)
        theta (PerturbationAssembly.pairChoice xs choice) mask = Product.bytes entries ∧
      Good ∅ u J entries ∧
      rawDenote p.ops.decode entries =
        specializedJet u J mask (fixedLowJet p ps P n f j theta choice) := by
  let pairs := PerturbationAssembly.pairChoice xs choice
  have hpairs : pairs.length = n :=
    (PerturbationAssembly.pairChoice_length xs choice (hx.trans hc.symm)).trans hx
  let source := QueryProducerSpace.emittedSource p.t p.model p.modulus p.cache
    J (p.R + 1) theta pairs
  have hvalid : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1 :=
    QueryProducerSpace.incidence_valid p.ops u J hu hJ theta _ _
  have hsources := PerturbationAssembly.sourceRows_nativeStored p ps P u J n f j hu hJ
    theta xs hx choice hc hs
  change PerturbationAssembly.castJet hpairs (rawDenote p.ops.decode source) =
    Squarefree.canonical u J (fixedLowJet p ps P n f j theta choice) at hsources
  exact specialized_source_realizes 3 p.t p.modulus p.cache
    (LiftRing.of (p.model.F p.t)) (RingBasis.basis (p.model.F p.t))
    u J mask source hpairs hvalid (fixedLowJet p ps P n f j theta choice) hsources


/-- High coordinates return the physically stored scalar zero or one, with the
same origin encoding used by the low producer. -/
theorem constant_payload_realizes {n B d : ℕ} (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (f : RingProgram.Code (Word B) d → R) (c : RingProgram.Code (Word B) d)
    (mask : List Bool) :
    ∃ entries : List (Product.Entry n B d),
      Encoding.frame (PerturbationAssembly.originKey n) ++ Encoding.frame (RingProgram.flat c) =
        Product.bytes entries ∧ Good ∅ u J entries ∧
      rawDenote f entries = specializedJet u J mask (Squarefree.Sparse.atom Squarefree.Index.origin (f c)) := by
  refine ⟨Squarefree.Sparse.constant u J c, ?_, constant_good u J c, ?_⟩
  · rw [show Squarefree.Sparse.constant (V := Fin n) u J c = [(Squarefree.Index.origin, c)] by
      simp [Squarefree.Sparse.constant, hu, hJ]]
    exact (PerturbationAssembly.origin_dictionary n c).trans
      (QueryProducerSpace.dictionaryBits_productBytes _)
  · rw [rawDenote_constant, specializedJet_atom_origin]

/-- The actual producer's branch-sensitive bytes admit a valid typed witness
with the fixed source meaning. No coefficient values are supplied by a caller. -/
theorem payload_realizes {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (s : FactorTableProgram.OuterStore)
    (payload : List Bool) (hc : (s 546).length = n)
    (hz : s 547 = RingProgram.flat p.ops.zeroRun.1)
    (ho : s 548 = RingProgram.flat p.ops.oneRun.1)
    (h : FactorTableNative.PayloadMeaning p ps P u J n f theta s j payload) :
    ∃ entries : List (Product.Entry n (baseWidth 3 p.t) d),
      payload = Product.bytes entries ∧ Good ∅ u J entries ∧
      rawDenote p.ops.decode entries = specializedJet u J (s 857)
        (PerturbationAssembly.sourceIncidenceJet p ps P n f j theta
          (FactorTableProgram.projectBase s)) := by
  have hsource := h.source
  cases hb : (s 574).getD j false
  · simp only [hb, Bool.false_eq_true, ite_false] at hsource
    obtain ⟨xs, hx, hs, hpayload⟩ := hsource
    obtain ⟨entries, hbytes, hgood, hmeaning⟩ :=
      low_payload_realizes p ps P u J n f j hu hJ theta xs hx (s 546) (s 857) hc hs
    refine ⟨entries, hpayload.trans hbytes, hgood, ?_⟩
    simpa only [PerturbationAssembly.sourceIncidenceJet,
      show FactorTableProgram.projectBase s 574 = s 574 from rfl,
      show FactorTableProgram.projectBase s 546 = s 546 from rfl,
      hb, Bool.false_eq_true, ite_false, fixedLowJet] using hmeaning
  · simp only [hb, ite_true] at hsource
    let c := if (s 575).getD j false then p.ops.oneRun.1 else p.ops.zeroRun.1
    have hbytes : payload = Encoding.frame (PerturbationAssembly.originKey n) ++
        Encoding.frame (RingProgram.flat c) := by
      rw [hsource]
      cases hh : (s 575).getD j false <;>
        simp only [c, hh, Bool.false_eq_true, ite_false, ite_true, hz, ho]
    have hvalue : p.ops.decode c = if (s 575).getD j false then 1 else 0 := by
      cases hh : (s 575).getD j false <;>
        simp only [c, hh, Bool.false_eq_true, ite_false, ite_true,
          p.ops.one_correct, p.ops.zero_correct]
    obtain ⟨entries, he, hg, hv⟩ := constant_payload_realizes (n := n) u J hu hJ p.ops.decode c (s 857)
    refine ⟨entries, hbytes.trans he, hg, ?_⟩
    rw [hvalue] at hv
    simpa only [PerturbationAssembly.sourceIncidenceJet,
      show FactorTableProgram.projectBase s 574 = s 574 from rfl,
      show FactorTableProgram.projectBase s 575 = s 575 from rfl,
      hb, ite_true] using hv

/-- Exact physical byte decoding transports the source meaning to the same
entries consumed by the actual arithmetic run. No semantic encoding
injectivity or extra validity premise is required. -/
theorem payload_typed_correct {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (s : FactorTableProgram.OuterStore)
    (payload : List Bool) (hc : (s 546).length = n)
    (hz : s 547 = RingProgram.flat p.ops.zeroRun.1)
    (ho : s 548 = RingProgram.flat p.ops.oneRun.1)
    (h : FactorTableNative.PayloadMeaning p ps P u J n f theta s j payload)
    (entries : List (Product.Entry n (baseWidth 3 p.t) d))
    (hbytes : payload = Product.bytes entries) :
    Good ∅ u J entries ∧
      rawDenote p.ops.decode entries = specializedJet u J (s 857)
        (PerturbationAssembly.sourceIncidenceJet p ps P n f j theta
          (FactorTableProgram.projectBase s)) := by
  obtain ⟨semantic, hs, hg, hv⟩ :=
    payload_realizes p ps P u J n f j hu hJ theta s payload hc hz ho h
  have he : entries = semantic := product_bytes_injective
    (Nat.mul_pos p.ht (Nat.zero_lt_succ _)) (hbytes.symm.trans hs)
  simpa only [he] using And.intro hg hv

/-- The concrete scalar decoder and multiplication table are those of the
same source ring that produced the cached coefficient words. -/
theorem source_context_decode {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n u J : ℕ) (width : List Bool) (hw : width.length = baseWidth 3 p.t) :
    RingProgram.denote
      (RingProgram.scalarRing 3 p.t (LeafProgram.Factor.sourceContext p n u J width hw).modulus
        (LeafProgram.Factor.sourceContext p n u J width hw).cache)
      (LiftRing.of (p.model.F p.t)) (RingBasis.basis (p.model.F p.t)) = p.ops.decode := rfl

/-- Paid cache setup identifies the actual source context, encoded ring unit,
negative unit, and idempotent tape. All assumptions are physical master words;
the table law and coefficient meanings come from the same produced source ring. -/
theorem setup_source_context {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (width : List Bool) (hw : width.length = baseWidth 3 p.t)
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (a : FactorAssignmentProgram.Data)
    (hempty : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hn : (a.stacks 128).length = n)
    (hm : a.stacks 194 = p.modulus.bits)
    (hwidth : a.stacks 202 = width) (hz : a.stacks 203 = p.cache.zero.val)
    (htable : a.stacks 201 = RingTriple.tableEncoding
      (HornerProgram.modelTable p.t p.model p.modulus p.cache))
    (hdegree : a.stacks 204 = List.replicate d true)
    (hprec : a.stacks 212 = List.replicate u true)
    (hjet : a.stacks 243 = List.replicate J true)
    (hone : a.stacks 207 = RingProgram.flat p.ops.oneRun.1)
    (hminus : a.stacks 211 = RingProgram.flat p.minusOne)
    (hdigits : a.stacks 281 = IdempotentApplyProgram.triplesTape digits) :
    ∃ b, StructuredCalls.Eval FactorAssignmentProgram.setup
        (FactorAssignmentProgram.setupCost a) a b ∧
      (∀ i : Fin 56, b.stacks (i.castAdd 840) = IdempotentApplyProgram.Steps.low
        (LeafProgram.Factor.sourceContext p n u J width hw) i) ∧
      b.stacks 69 = Product.bytes (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) ∧
      LeafProgram.NativeSemantics.Good ∅ u J (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) ∧
      rawDenote p.ops.decode (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) =
        Squarefree.canonical u J 1 ∧
      rawValue u J p.ops.decode (FactorAssignmentProgram.oneEntries (n := n) p.ops.oneRun.1) = 1 ∧
      b.stacks 76 = RingProgram.flat p.minusOne ∧ p.ops.decode p.minusOne = -1 ∧
      b.stacks 143 = IdempotentApplyProgram.triplesTape digits ∧
      (b.stacks 88).length = n ∧
      (∀ i j : Fin d, RingBasis.basis (p.model.F p.t) i * RingBasis.basis (p.model.F p.t) j =
        ∑ k, LiftRing.of (p.model.F p.t)
          (wordValue 3 p.t ((LeafProgram.Factor.sourceContext p n u J width hw).table i j k)) *
            RingBasis.basis (p.model.F p.t) k) ∧
      ∀ i : Fin 896, i ∉ FactorAssignmentProgram.cachePorts.map FactorAssignmentProgram.lowStack →
        b.stacks i = a.stacks i := by
  obtain ⟨b, he, hlo, hunit, hgood, hframe⟩ :=
    FactorAssignmentProgram.setup_context a p.ops.oneRun.1 u J hu hJ hempty hn hone
  obtain ⟨c, hec, hcache, _⟩ := FactorAssignmentProgram.setup_eval a
  have hcb : c = b := StructuredCalls.Eval.final_unique 0 hec he
  have copied (pair : Fin 768 × Fin 768) (hp : pair ∈ LeafNodeCacheProgram.directCopies) :
      b.stacks (FactorAssignmentProgram.lowStack pair.2) =
        a.stacks (FactorAssignmentProgram.lowStack pair.1) := by
    rw [← hcb]
    exact (hcache pair.2).trans (FactorAssignmentProgram.setup_direct_word _ pair hp)
  refine ⟨b, he, ?_, hunit, hgood, ?_, oneEntries_rawValue u J _ _ p.ops.one_correct,
    ?_, p.hminus, ?_, ?_, LeafProgram.NativeSemantics.model_table_correct p.t p.ht p.hd p.model p.modulus p.cache,
    hframe⟩
  · intro i
    rw [hlo i, hm, hwidth, hz, htable, hdegree, hprec, hjet]
    rfl
  · rw [FactorAssignmentProgram.oneEntries_eq_constant _ u J hu hJ,
      rawDenote_constant, p.ops.one_correct, Squarefree.Sparse.atom_origin_one]
  · exact (copied (211,76) (by decide)).trans hminus
  · exact (copied (281,143) (by decide)).trans hdigits
  · exact (congrArg List.length (copied (128,88) (by decide))).trans hn

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
