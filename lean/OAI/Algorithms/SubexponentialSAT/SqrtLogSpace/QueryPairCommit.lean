import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

/-! The signed finite-difference term is committed to the actual node word.
The pair product and the node sum use the same stored dictionaries as their
validity and readout witnesses. Marker readout remains additive. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram
open TruncatedRingProgram QueryProgram QueryTupleState

abbrev Data := State 40 896

/-- The actual node dictionary, after additive shared-marker readout. -/
structure NodeAccumulatorMeaning {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (value : Truncated (q.p.model.O q.p.t) q.J) (a : Data) : Prop where
  entries : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    a.stacks 850=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      Dense.readout (rawValue q.p.t q.J q.p.ops.decode entries)=value

namespace NodeAccumulatorMeaning

theorem zero {r Q n d : ℕ} (q : Factor.Spec r Q n d) (a : Data)
    (hz : a.stacks 850=[]) : NodeAccumulatorMeaning q 0 a := by
  refine ⟨[],hz,Good.nil,?_⟩
  rw [rawValue_nil,map_zero]

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : NodeAccumulatorMeaning q value a) (hf : b.stacks 850=a.stacks 850) :
    NodeAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

theorem word_length_le {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a : Data}
    (h : NodeAccumulatorMeaning q value a) :
    (a.stacks 850).length≤
      q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) := by
  obtain ⟨entries,he,hg,_⟩ := h.entries
  rw [he]
  exact empty_bytes_length_le hg

end NodeAccumulatorMeaning

/-- Additive readout commutes with the integer sign. No multiplicativity of
marker readout is asserted or used. -/
theorem readout_neg_one_pow_mul {R : Type*} [CommRing R] {t J : ℕ}
    (k : ℕ) (x : Dense R t J) :
    Dense.readout ((-1 : Dense R t J)^k*x)=
      (-1 : Truncated R J)^k*Dense.readout x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_assoc,neg_one_mul,map_neg,ih,
      pow_succ',mul_assoc,neg_one_mul]

/-- The coefficient-ring decoder and multiplication table are those of the
actual produced ternary ring. The sign scans the two physical pair masks. -/
theorem signed_readout {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (E U : List Bool) (hU : U.count true≤E.count true)
    (source seed : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hseed : Good ∅ q.p.t q.J seed) :
    Dense.readout (rawValue q.p.t q.J q.p.ops.decode
      (signedSum 3 q.p.t q.p.modulus q.p.cache q.ctx.table q.minus
        (parity U (parity E false)) source seed)) =
      (-1 : Truncated (q.p.model.O q.p.t) q.J)^(E.count true-U.count true)*
        Dense.readout (rawValue q.p.t q.J q.p.ops.decode source)+
        Dense.readout (rawValue q.p.t q.J q.p.ops.decode seed) := by
  have hv := pair_signedSum_dense 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.ctx.table (Factor.Semantics.context_table_correct q.p q.u q.J q.width q.widthLength)
    q.p.t q.J q.minus q.minusValue E U hU source seed hseed.nodup
  change rawValue q.p.t q.J q.p.ops.decode _ =
    (-1 : Dense (q.p.model.O q.p.t) q.p.t q.J)^(E.count true-U.count true)*
      rawValue q.p.t q.J q.p.ops.decode source+
      rawValue q.p.t q.J q.p.ops.decode seed at hv
  rw [hv,map_add,readout_neg_one_pow_mul]

theorem ready_environment {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a : Data}
    (h : QueryReady q node H high E U P a) :
    QueryAssembler.pairEnvironment a=Squarefree.ScaleProgram.environment 3 q.p.t
      q.p.modulus q.p.cache q.ctx.table q.minus (List.replicate d true) q.width := by
  simp only [QueryAssembler.pairEnvironment,h.modulus,h.width,h.scalarZero,h.table,
    h.minus,h.degree]
  rfl

/-- The actual commit changes its node word while retaining every physical
input inspected by the next pair. -/
theorem ready_frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a)
    (hf : ∀ i,i∉QueryAssembler.pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf 128 (by decide) (by decide) (by decide)).trans h.ambient
    theta := (hf 78 (by decide) (by decide) (by decide)).trans h.theta
    modulus := (hf 194 (by decide) (by decide) (by decide)).trans h.modulus
    table := (hf 201 (by decide) (by decide) (by decide)).trans h.table
    width := (hf 202 (by decide) (by decide) (by decide)).trans h.width
    scalarZero := (hf 203 (by decide) (by decide) (by decide)).trans h.scalarZero
    degree := (hf 204 (by decide) (by decide) (by decide)).trans h.degree
    one := (hf 207 (by decide) (by decide) (by decide)).trans h.one
    minus := (hf 211 (by decide) (by decide) (by decide)).trans h.minus
    precision := (hf 212 (by decide) (by decide) (by decide)).trans h.precision
    order := (hf 243 (by decide) (by decide) (by decide)).trans h.order
    zero := (hf 280 (by decide) (by decide) (by decide)).trans h.zero
    code := (hf 281 (by decide) (by decide) (by decide)).trans h.code
    clauses := (hf 700 (by decide) (by decide) (by decide)).trans h.clauses
    rows := (hf 701 (by decide) (by decide) (by decide)).trans h.rows
    rowCount := (hf 704 (by decide) (by decide) (by decide)).trans h.rowCount
    markedIndex := (hf 705 (by decide) (by decide) (by decide)).trans h.markedIndex
    markedFlag := (hf 706 (by decide) (by decide) (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf 707 (by decide) (by decide) (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf 708 (by decide) (by decide) (by decide))).trans h.indexWidth
    highMask := (hf 702 (by decide) (by decide) (by decide)).trans h.highMask
    highBits := (hf 703 (by decide) (by decide) (by decide)).trans h.highBits
    outer := (hf 858 (by decide) (by decide) (by decide)).trans h.outer
    inner := (hf 857 (by decide) (by decide) (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf 130 (by decide) (by decide) (by decide)).trans h.colors
    nodes := (hf 131 (by decide) (by decide) (by decide)).trans h.nodes
    typeWidth := (hf 132 (by decide) (by decide) (by decide)).trans h.typeWidth
    positive := (hf 710 (by decide) (by decide) (by decide)).trans h.positive
    negative := (hf 711 (by decide) (by decide) (by decide)).trans h.negative
    sourceWidth := (hf 140 (by decide) (by decide) (by decide)).trans h.sourceWidth
    power := (hf 712 (by decide) (by decide) (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf 138 (by decide) (by decide) (by decide)).trans h.radius
    offset := (hf 139 (by decide) (by decide) (by decide)).trans h.offset
    metadata := (hf 135 (by decide) (by decide) (by decide)).trans h.metadata
    plans := (hf 136 (by decide) (by decide) (by decide)).trans h.plans
    inverses := (hf 713 (by decide) (by decide) (by decide)).trans h.inverses
    negatives := (hf 714 (by decide) (by decide) (by decide)).trans h.negatives
    differences := (hf 715 (by decide) (by decide) (by decide)).trans h.differences
    ringWidth := (hf 717 (by decide) (by decide) (by decide)).trans h.ringWidth
    rowWidth := (hf 716 (by decide) (by decide) (by decide)).trans h.rowWidth
    inverseDenominator := (hf 728 (by decide) (by decide) (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hs : p.1.castAdd 128∉QueryAssembler.pairScratch ∧
        p.1.castAdd 128≠(850:Fin 896) ∧ p.1.castAdd 128≠(851:Fin 896) := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf _ hs.1 hs.2.1 hs.2.2]
    exact h.cacheCaps p hp
  · rw [hf 128 (by decide) (by decide) (by decide)]
    exact h.ambientCap
  · rw [hf 207 (by decide) (by decide) (by decide)]
    exact h.oneCap

/-- Transporting a support through the actual free-coordinate enumeration
preserves its cardinality, including the empty free domain. -/
theorem free_image_card {n : ℕ} (H : Finset (Fin n))
    (E : Finset (Fin (n-H.card))) :
    (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val)).card=E.card := by
  apply Finset.card_image_of_injective
  intro i j hij
  exact (HighIncidenceProgram.freeOrder H).injective (Subtype.ext hij)

open CommandRegisterFrames

private theorem not_mem_union {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} (hl : i ∉ left) (hr : i ∉ right) :
    i ∉ left ∪ right := by
  simpa only [Finset.mem_union, not_or] using And.intro hl hr

/-- The real sign scan, arithmetic calls and cleanup write only the low
register bank. Suspended pair and high-assignment controllers survive. -/
theorem command_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i∉writes QueryAssembler.commitPair := by
  have h0 : i≠0 := by intro h; subst i; omega
  have h1 : i≠1 := by intro h; subst i; omega
  have hout16 : ¬∃j,FactorEnvironment.registerMap j=i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  have hout8 : ¬∃j,leafArithmeticRegs j=i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  have hout3 : ¬∃j,pairRegisters j=i := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega
  have hclear : i∉writes QueryAssembler.clearPair :=
    not_mem_liftCommand _ _ _ _ _ i hout16
  have hboot : i∉writes FactorEnvironment.bootstrap :=
    not_mem_liftCommand _ _ _ _ _ i hout16
  have hoverwrite : i∉writes (QueryTupleVisitor.overwrite 211 34) :=
    not_mem_union (not_mem_clearProgram _ _ _ i h0 h1)
      (not_mem_copyProgram _ _ _ _ _ i h0 h1)
  have hsign : i∉writes pairSignCall := not_mem_liftProgram _ _ _ i hout3
  have hscale : i∉writes signedAccumulate :=
    not_mem_union (not_mem_liftProgram _ _ _ i hout8)
      (not_mem_liftProgram _ _ _ i hout8)
  have hpop : i∉writes (.base (.atom (.pop (848:Fin 896) (0:Fin 40) 1))) := by
    simp [writes,baseWrites,StructuredProgram.Atom.instr,ProgramLogic.registerWrites,h0,h1]
  exact not_mem_union (not_mem_union hclear (not_mem_union hboot hoverwrite))
    (not_mem_union (not_mem_union hsign (not_mem_union hscale hpop)) hclear)

theorem register_frame {steps : ℕ} {a b : Data}
    (he : Eval QueryAssembler.commitPair steps a b) (i : Fin 40) (hi : 16 ≤ i.val) :
    b.regs i=a.regs i := eval_register_frame he i (command_not_mem_writes i hi)

/-- Every source prefix preserves the caller controller registers. -/
theorem prefix_register_frame {steps : ℕ}
    {a b : Cfg 40 896 (size QueryAssembler.commitPair+1)}
    (he : Trace QueryAssembler.commitPairProgram steps a b)
    (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i=a.regs i :=
  compiled_trace_register_frame _ _ _ he i (command_not_mem_writes i hi)

/-- One real native commit, with the sign derived from the exact encoded
supports emitted by the bounded-memory pair traversal. All boundary, time,
and prefix conclusions concern this same execution. -/
theorem run {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool)
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E) (P B : ℕ) (a : Data)
    (hready : QueryReady q node H high
      (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
      (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P a)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (pairValue nodeValue : Truncated (q.p.model.O q.p.t) q.J)
    (hpair : PairAccumulatorMeaning q pairValue a)
    (hnode : NodeAccumulatorMeaning q nodeValue a)
    (hb : ∀ i,(a.stacks i).length≤B)
    (hcapacity : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2)≤B) :
    ∃ steps b, Eval QueryAssembler.commitPair steps a b ∧
      NodeAccumulatorMeaning q (nodeValue+(-1)^ (E.card-U.card)*pairValue) b ∧
      QueryReady q node H high
        (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
        (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P b ∧
      b.stacks 851=[] ∧
      (∀ i,i∉QueryAssembler.pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) ∧
      (∀ i,(b.stacks i).length≤B) ∧
      steps+1≤51000*(B+1)+pairUpdateBudget n (baseWidth 3 q.p.t) d q.p.t q.J
        (a.stacks 834).length (a.stacks 835).length ∧
      Trace QueryAssembler.commitPairProgram (steps+1)
        (a.withPC (some QueryAssembler.commitPairProgram.entry)) (b.withPC none) ∧
      ∀ (prefixSteps : ℕ) intermediate, prefixSteps ≤ steps + 1 →
        Trace QueryAssembler.commitPairProgram prefixSteps
          (a.withPC (some QueryAssembler.commitPairProgram.entry)) intermediate →
        ∀ i,(intermediate.stacks i).length≤896*B+51000*(B+1)+
          pairUpdateBudget n (baseWidth 3 q.p.t) d q.p.t q.J
            (a.stacks 834).length (a.stacks 835).length := by
  obtain ⟨source,hsource,hsourceGood,hsourceValue⟩ := hpair.entries
  obtain ⟨seed,hseed,hseedGood,hseedValue⟩ := hnode.entries
  have hEcount : (a.stacks 834).count true=E.card := by
    rw [he,DifferencePairs.encodePair_outer_count]
  have hUcount : (a.stacks 835).count true=U.card := by
    rw [hu,DifferencePairs.encodePair_inner_count E U hU]
  have hcount : (a.stacks 835).count true≤(a.stacks 834).count true := by
    rw [hEcount,hUcount]
    exact Finset.card_le_card hU
  obtain ⟨steps,b,hex,hgood,h850,h851,hframe,hbound,htime,htrace,hspace⟩ :=
    QueryAssembler.commitPair_eval 3 q.p.t q.p.modulus q.p.cache q.p.hz
      q.ctx.table q.minus source seed hsourceGood hseedGood
      (List.replicate d true) q.width (List.length_replicate ..) q.widthLength
      a B (ready_environment hready) hsource hseed hb hcapacity
  refine ⟨steps,b,hex,?_,ready_frame hready hframe,h851,hframe,hbound,htime,htrace,hspace⟩
  refine ⟨_,h850,hgood,?_⟩
  rw [signed_readout q (a.stacks 834) (a.stacks 835) hcount source seed hseedGood,
    hsourceValue,hseedValue,hEcount,hUcount,add_comm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
