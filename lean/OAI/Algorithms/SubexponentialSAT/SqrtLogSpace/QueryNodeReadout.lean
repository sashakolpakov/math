import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

/-! The actual node dictionary is read into increasing Taylor coefficients,
appended to the interpolation stream, and reclaimed before the next node.
The dictionary witness, encoded result and resource trace are shared. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram TruncatedRingProgram QueryTupleState
open QueryPairCommit QueryReadyConstruction

abbrev Data := State 40 896

private theorem coeff_getElem {R : Type*} [Semiring R] (xs : List R)
    (i : ℕ) (hi : i < xs.length) : PolynomialAlgorithm.coeff xs i = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

/-- Equal truncated coefficients identify the complete fixed-length list,
including retained zero coefficients. -/
theorem list_of_readout {R : Type*} [CommRing R] {J : ℕ}
    (xs : List R) (value : Truncated R J) (hl : xs.length=J)
    (hv : Truncated.ofPolynomial J (PolynomialAlgorithm.denote xs)=value) :
    xs=List.ofFn value.coeff := by
  apply List.ext_getElem (by simp [hl])
  intro i hi hj
  have hJ : i < J := by simpa [hl] using hi
  have hc := congrArg (fun v : Truncated R J => v.coeff ⟨i,hJ⟩) hv
  change (PolynomialAlgorithm.denote xs).coeff i=value.coeff ⟨i,hJ⟩ at hc
  rw [PolynomialAlgorithm.coeff_denote,coeff_getElem xs i hi] at hc
  simpa using hc

/-- Every readout cache comes from the actual retained query words. -/
theorem master_common {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool}
    {P : ℕ} {a : Data}
    (h : CommonReady q node H high P a)
    (entries : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (he : a.stacks 850=Product.bytes entries) :
    NodeAppendSpace.MasterReady a q.p.modulus.bits q.width (List.replicate d true)
      (Product.bytes entries) (RingProgram.flat q.p.ops.zeroRun.1)
      (List.replicate q.p.t true) (List.replicate q.J true) (List.replicate n true) :=
  ⟨h.modulus,h.width,h.degree,he,h.zero,h.precision,h.order,h.ambient⟩

/-- Every readout cache comes from the actual retained query words. -/
theorem master_ready {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P : ℕ} {a : Data}
    (h : QueryReady q node H high E U P a)
    (entries : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (he : a.stacks 850=Product.bytes entries) :
    NodeAppendSpace.MasterReady a q.p.modulus.bits q.width (List.replicate d true)
      (Product.bytes entries) (RingProgram.flat q.p.ops.zeroRun.1)
      (List.replicate q.p.t true) (List.replicate q.J true) (List.replicate n true) :=
  master_common (common_of_ready h) entries he

/-- The produced native coefficient words represent exactly the node's
additive shared-marker readout, in increasing Taylor order. -/
theorem codes_value {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (entries : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hg : Good ∅ q.p.t q.J entries)
    (value : Truncated (q.p.model.O q.p.t) q.J)
    (hv : Dense.readout (rawValue q.p.t q.J q.p.ops.decode entries)=value) :
    let codes := MomentsReadoutProgram.outputCodes 3 q.p.t q.p.modulus q.p.cache
      entries q.p.t q.p.ops.zeroRun.1 0 q.J
    codes.length=q.J ∧ codes.map q.p.ops.decode=List.ofFn value.coeff := by
  dsimp only
  have hlist := MomentsReadoutProgram.outputCodes_denote 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    entries q.p.t q.J q.p.ops.zeroRun.1 hg.nodup q.p.ops.zero_correct
  have hlen := congrArg List.length hlist
  simp only [List.length_map,Moments.outputCoefficients_length] at hlen
  refine ⟨hlen,list_of_readout _ value (by simpa using hlen) ?_⟩
  have hread := readout_codes_dense 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.p.t q.J entries q.p.ops.zeroRun.1 hg.nodup q.p.ops.zero_correct
  exact hread.trans hv

/-- Read, serialize, append and finish one completed interpolation node.
All zero Taylor slots remain in the actual stream; the next node index and
cursor guard are updated by paid native instructions. -/
theorem run_common {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool)
    (P B index : ℕ) (a : Data)
    (hready : CommonReady q node H high P a)
    (value : Truncated (q.p.model.O q.p.t) q.J)
    (hvalue : NodeAccumulatorMeaning q value a)
    (remaining : List (List Bool))
    (hcursor : a.stacks 301=Encoding.encodeList id remaining)
    (hindex : a.stacks 307=List.replicate index true)
    (hb : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + q.J * (d * baseWidth 3 q.p.t) ≤ B)
    (hnext : index + 1 ≤ B) :
    ∃ steps b, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 q.p.t)) d),
      Eval QueryNodeFinish.command steps a b ∧ codes.length=q.J ∧
      codes.map q.p.ops.decode=List.ofFn value.coeff ∧
      b.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      b.stacks 78=[] ∧ b.stacks 850=[] ∧ b.stacks 862=[] ∧
      (∀ i∈NodeReadoutSpace.scratchPorts,b.stacks i=[]) ∧
      b.stacks 307=List.replicate (index+1) true ∧
      b.regs 37= !remaining.isEmpty ∧ b.regs 38=true ∧
      (∀ i,i∉QueryNodeFinish.touchedPorts → b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps + 1 ≤ QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B ∧
      Trace QueryNodeFinish.program (steps + 1)
        (a.withPC (some QueryNodeFinish.program.entry)) (b.withPC none) ∧
      ∀ (prefixSteps : ℕ) intermediate, prefixSteps ≤ steps + 1 →
        Trace QueryNodeFinish.program prefixSteps
          (a.withPC (some QueryNodeFinish.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * B + QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B := by
  obtain ⟨entries,h850,hgood,hmeaning⟩ := hvalue.entries
  have hr := master_common hready entries h850
  have hx : (a.stacks 307).length + 1 ≤ B := by simpa [hindex] using hnext
  obtain ⟨steps,rr,ht,he,hbits,hbound⟩ := QueryNodeFinish.command_eval
    3 q.p.t q.p.modulus q.p.cache entries hgood q.p.ops.zeroRun.1
    q.width (List.replicate d true) (List.replicate q.p.t true)
    (List.replicate q.J true) (List.replicate n true)
    (List.length_replicate ..) q.widthLength (List.length_replicate ..)
    (List.length_replicate ..) (List.length_replicate ..) a B hb hr hout hx
  let codes := MomentsReadoutProgram.outputCodes 3 q.p.t q.p.modulus q.p.cache
    entries q.p.t q.p.ops.zeroRun.1 0 q.J
  let bits := (codes.map RingProgram.flat).flatten
  let b := QueryNodeFinish.result a rr q.p.modulus.bits q.width (List.replicate d true)
    (Product.bytes entries) (RingProgram.flat q.p.ops.zeroRun.1)
    (List.replicate q.p.t true) (List.replicate q.J true) (List.replicate n true) bits
  have hc := codes_value q entries hgood value hmeaning
  have h78 : b.stacks 78=[] := by
    simp [b,QueryNodeFinish.result,QueryNodeFinish.finished_stacks]
  have hnode : b.stacks 850=[] := by
    simp [b,QueryNodeFinish.result,QueryNodeFinish.finished_stacks]
  have hempty (i : Fin 896) (hi : i=862 ∨ i∈NodeReadoutSpace.scratchPorts) :
      b.stacks i=[] := by
    have h78 : i≠78 := by
      rcases hi with rfl|hi
      · decide
      · have hh := NodeReadoutSpace.scratchPorts_low hi
        intro heq
        subst i
        change 88≤78 ∧ 78<128 at hh
        omega
    have h850 : i≠850 := by
      rcases hi with rfl|hi
      · decide
      · have hh := NodeReadoutSpace.scratchPorts_low hi
        intro heq
        subst i
        change 88≤850 ∧ 850<128 at hh
        omega
    have h307 : i≠307 := by
      rcases hi with rfl|hi
      · decide
      · have hh := NodeReadoutSpace.scratchPorts_low hi
        intro heq
        subst i
        change 88≤307 ∧ 307<128 at hh
        omega
    rw [show b.stacks i=(NodeAppendSpace.result a rr q.p.modulus.bits q.width
      (List.replicate d true) (Product.bytes entries) (RingProgram.flat q.p.ops.zeroRun.1)
      (List.replicate q.p.t true) (List.replicate q.J true) (List.replicate n true) bits).stacks i
      from QueryNodeFinish.finished_frame _ i h78 h850 h307]
    exact NodeAppendSpace.result_empty a rr _ _ _ _ _ _ _ _ _ hr i hi
  have hguard := QueryNodeFinish.result_guard a rr _ _ _ _ _ _ _ _ bits hr remaining hcursor
  refine ⟨steps,b,codes,he,hc.1,hc.2,
    QueryNodeFinish.result_output a rr _ _ _ _ _ _ _ _ _ hr,h78,hnode,
    hempty 862 (Or.inl rfl),fun i hi => hempty i (Or.inr hi),
    QueryNodeFinish.result_index a rr _ _ _ _ _ _ _ _ _ hr index hindex,
    hguard.1,hguard.2,QueryNodeFinish.result_frame a rr _ _ _ _ _ _ _ _ _ hr,
    hbound,ht,compiled_halt_trace he 850 863,?_⟩
  intro prefixSteps intermediate hle htrace i
  exact StructuredSpace.local_stack_bound QueryNodeFinish.program
    (StreamResources.dataBits_le_mul _ hb) prefixSteps intermediate (hle.trans ht) htrace i

/-- The original pair-specific entry remains an immediate specialization. -/
theorem run {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n))
    (P B index : ℕ) (a : Data)
    (hready : QueryReady q node H high E U P a)
    (value : Truncated (q.p.model.O q.p.t) q.J)
    (hvalue : NodeAccumulatorMeaning q value a)
    (remaining : List (List Bool))
    (hcursor : a.stacks 301=Encoding.encodeList id remaining)
    (hindex : a.stacks 307=List.replicate index true)
    (hb : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + q.J * (d * baseWidth 3 q.p.t) ≤ B)
    (hnext : index + 1 ≤ B) :
    ∃ steps b, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 q.p.t)) d),
      Eval QueryNodeFinish.command steps a b ∧ codes.length=q.J ∧
      codes.map q.p.ops.decode=List.ofFn value.coeff ∧
      b.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      b.stacks 78=[] ∧ b.stacks 850=[] ∧ b.stacks 862=[] ∧
      (∀ i∈NodeReadoutSpace.scratchPorts,b.stacks i=[]) ∧
      b.stacks 307=List.replicate (index+1) true ∧
      b.regs 37= !remaining.isEmpty ∧ b.regs 38=true ∧
      (∀ i,i∉QueryNodeFinish.touchedPorts → b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps + 1 ≤ QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B ∧
      Trace QueryNodeFinish.program (steps + 1)
        (a.withPC (some QueryNodeFinish.program.entry)) (b.withPC none) ∧
      ∀ (prefixSteps : ℕ) intermediate, prefixSteps ≤ steps + 1 →
        Trace QueryNodeFinish.program prefixSteps
          (a.withPC (some QueryNodeFinish.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * B + QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B :=
  run_common q node H high P B index a (common_of_ready hready) value hvalue
    remaining hcursor hindex hb hout hnext

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout
