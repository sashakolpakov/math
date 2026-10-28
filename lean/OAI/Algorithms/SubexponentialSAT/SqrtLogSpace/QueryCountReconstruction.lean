import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata

/-! The coefficients emitted by the actual ordered node loop determine the
same fixed-length Hermite inputs consumed by the native reconstruction tail.
No canonical choice of coefficient bytes across node states is required. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open Polynomial DensePolynomialProgram LeafProgram LeafParametersProgram

/-- Package the very coefficient words emitted at each node. The witness
selection is proof-only; the actual machine already retained their flat bytes. -/
theorem jets_of_outputs {A : Type*} [CommRing A] {width d Q J : ℕ}
    (ops : SubexpSymbolicCost.RepresentedRing (Coeff width d) A)
    (nodes : Fin Q → Coeff width d) (target : Polynomial A)
    (outputs : List (List Bool)) (hlen : outputs.length = Q)
    (houtputs : ∀ i : Fin Q, ∃ codes : List (Coeff width d),
      codes.length = J ∧
      codes.map ops.decode = List.ofFn
        (Truncated.ofPolynomial J (target.comp (X + C (ops.decode (nodes i))))).coeff ∧
      outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten) :
    ∃ jets : Fin Q → CRTLocalProgram.Model.Poly width d J,
      outputs.flatten = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)) ∧
      Reconstruction.HasJets ops nodes J (fun i => (jets i).val) target := by
  classical
  choose codes hlength hvalue hbits using houtputs
  let jets : Fin Q → CRTLocalProgram.Model.Poly width d J := fun i => ⟨codes i, hlength i⟩
  refine ⟨jets, ?_, ?_⟩
  · have hout : outputs = (List.finRange Q).map (fun i => Fixed.encode (jets i)) := by
      apply List.ext_getElem (by simp [hlen])
      intro i hi hj
      have hfinBound : i < (List.finRange Q).length := by simpa using hj
      have hiQ : i < Q := by simpa using hfinBound
      have hfin : (List.finRange Q)[i]'hfinBound = (⟨i, hiQ⟩ : Fin Q) := by
        apply Fin.ext
        simp
      rw [List.getElem_map, hfin]
      simpa only [jets, Fixed.encode, DensePolynomialProgram.encode] using hbits ⟨i, hiQ⟩
    rw [hout, List.flatMap_def]
  · apply Reconstruction.hasJets_of_coefficients
    intro i z hz
    change (PolynomialAlgorithm.denote ((codes i).map ops.decode)).coeff z = _
    rw [hvalue i, PolynomialAlgorithm.coeff_denote]
    have hcoeff (xs : List A) (j : ℕ) (hj : j < xs.length) :
        PolynomialAlgorithm.coeff xs j = xs[j] := by
      induction xs generalizing j with
      | nil => simp at hj
      | cons x xs ih =>
        cases j with
        | zero => rfl
        | succ j => exact ih j (by simpa using hj)
    rw [hcoeff (List.ofFn (Truncated.ofPolynomial J
      (target.comp (X + C (ops.decode (nodes i))))).coeff) z (by simpa using hz)]
    simp only [List.getElem_ofFn, Truncated.coeff_ofPolynomial]


/-- Each physical node output retains exactly all J coefficient words,
including zero coefficients. Every prefix of the stream therefore has the
same exact linear storage charge. -/
theorem outputs_take_length {width d J : ℕ} (outputs : List (List Bool))
    (houtputs : ∀ bits ∈ outputs, ∃ codes : List (Coeff width d),
      codes.length = J ∧ bits = (codes.map RingProgram.flat).flatten) (i : ℕ) :
    (outputs.take i).flatten.length = min i outputs.length * (J * (d * width)) := by
  rw [List.length_flatten]
  have hlength : ((outputs.take i).map List.length) =
      List.replicate (outputs.take i).length (J * (d * width)) := by
    apply List.map_eq_replicate_iff.mpr
    intro bits hbits
    obtain ⟨codes, hc, rfl⟩ := houtputs bits (List.mem_of_mem_take hbits)
    change (DensePolynomialProgram.encode codes).length = _
    simp [hc]
  rw [hlength]
  simp

open QueryReconstruction in
/-- The native recovery consumes exactly the ordered coefficient words emitted
by the node loop. Its Hermite certificate is derived from those same words. -/
theorem run_space_of_outputs (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (outputs : List (List Bool)) (hlen : outputs.length = m.val 21)
    (hstream : a.stacks 863 = outputs.flatten)
    (houtputs : ∀ i : Fin (m.val 21),
      ∃ codes : List (Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
        codes.length = m.val 42 ∧
        codes.map (RingProgram.modelRing (m.val 33) ht hd
          (IrreducibleSearch.data hd) M cache).decode = List.ofFn
          (Truncated.ofPolynomial (m.val 42) (target.comp (X + C
            ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
              (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)))))).coeff ∧
        outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten)
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧
      out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  obtain ⟨jets, hbytes, hhas⟩ := jets_of_outputs
    (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
    (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
    target outputs hlen houtputs
  exact QueryReconstruction.run_space_with_frame m ht hd M cache half e hp a
    hscratch hframe hnodes hQ hJ hfield hexponent jets (hstream.trans hbytes)
    target hdegree hhas count multiplicity ambient hcount hlarge hconstant B S ha
    hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize hcountsize

open QueryReconstruction in
/-- The native recovery consumes exactly the ordered coefficient words emitted
by the node loop. Its Hermite certificate is derived from those same words. -/
theorem run_space_of_outputs_with_full_frame (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (outputs : List (List Bool)) (hlen : outputs.length = m.val 21)
    (hstream : a.stacks 863 = outputs.flatten)
    (houtputs : ∀ i : Fin (m.val 21),
      ∃ codes : List (Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
        codes.length = m.val 42 ∧
        codes.map (RingProgram.modelRing (m.val 33) ht hd
          (IrreducibleSearch.data hd) M cache).decode = List.ofFn
          (Truncated.ofPolynomial (m.val 42) (target.comp (X + C
            ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
              (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)))))).coeff ∧
        outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten)
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧
      out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 896, i ∈ retainedPorts → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  obtain ⟨jets, hbytes, hhas⟩ := jets_of_outputs
    (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
    (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
    target outputs hlen houtputs
  exact QueryReconstruction.run_space_with_full_frame m ht hd M cache half e hp a
    hscratch hframe hnodes hQ hJ hfield hexponent jets (hstream.trans hbytes)
    target hdegree hhas count multiplicity ambient hcount hlarge hconstant B S ha
    hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize hcountsize

private theorem field_of_model (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) (m : Circuit.Model)
    (hm : m = PreparedSource.numeric q k lengths) :
    (produce (q.input k)).Q < 3^(m.val 34) := by
  rw [hm]
  exact PreparedSource.numeric_field q k lengths hg

private theorem order_of_model (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) (m : Circuit.Model)
    (hm : m = PreparedSource.numeric q k lengths) : 0 < m.val 42 := by
  rw [hm]
  exact QueryTargetMetadata.numeric_order_pos q k lengths hg

section ActualQuery

open PreparedSource QueryReconstruction

variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
    (hv : query.Valid)
    (first : MulticolorTypes.Word (Query.packingProblem query k hg).r
      (Query.packingProblem query k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem query k hg).r
      (Query.packingProblem query k hg).Q))
    (node : Fin (Query.packingProblem query k hg).Q) (lengths : Fin 8 → ℕ)
    (m : Circuit.Model) (hm : m = numeric query k lengths)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)

local notation "headsInput" => heads query k hg first tail node

variable (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads query k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads query k hg first tail node).R) (heads query k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (source : List (List (SAT.Literal (Fin (heads query k hg first tail node).n))))
    (hsource : query.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "factor" => nativeSpecOfInputs headsInput m ht hd words hc M cache half e hp
  (field_of_model query k lengths hg m hm) query hv (Circuit.Model.val m 42)
  (order_of_model query k lengths hg m hm) source hsource

/-- The authentic native source and produced precision determine the recovered
natural count. No target-value, degree, no-wrap, or HasJets service is supplied. -/
theorem query_run_space (H : Finset (Fin (headsInput).n)) (high : H → Bool)
    (hwidth : ∀ clause ∈ source, clause.length ≤ k)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (outputs : List (List Bool)) (hlen : outputs.length = m.val 21)
    (hstream : a.stacks 863 = outputs.flatten)
    (houtputs : ∀ i : Fin (m.val 21),
      ∃ codes : List (Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
        codes.length = m.val 42 ∧
        codes.map (RingProgram.modelRing (m.val 33) ht hd
          (IrreducibleSearch.data hd) M cache).decode = List.ofFn
          (Truncated.ofPolynomial (m.val 42)
            ((NodeConcrete.specTarget factor H high).comp (X + C
              ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
                (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)))))).coeff ∧
        outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten)
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hambient : (headsInput).n + 1 ≤ B) :
    let count := NodeSemantics.ternaryFixedHighCount H high
      (NodeConcrete.sourceHashes factor) (factor).marked (factor).markedClause
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧ out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  dsimp only
  have hQ : 0 < m.val 21 := by
    rw [hm, numeric_Q]
    have hh := hg.2.2.2.2.2.2.1
    omega
  have hfield : m.val 21 < 3^(m.val 34) := by
    rw [hm, numeric_Q]
    exact numeric_field query k lengths hg
  have hdegree : (NodeConcrete.specTarget factor H high).natDegree < m.val 21 * m.val 42 := by
    subst m
    exact QueryTargetMetadata.actual_target_degree_executed query hv k hg
      first tail node lengths words hc M cache half e hp source hsource hwidth H high
  have hconstant := QueryTargetMetadata.native_count headsInput m ht hd words hc
    M cache half e hp (field_of_model query k lengths hg m hm) query hv (m.val 42)
    (order_of_model query k lengths hg m hm) source hsource H high
  have hcount := QueryTargetMetadata.native_count_le headsInput m ht hd words hc
    M cache half e hp (field_of_model query k lengths hg m hm) query hv (m.val 42)
    (order_of_model query k lengths hg m hm) source hsource H high
  have hlarge : 1 * 2^(headsInput).n < 3^(m.val 33) := by
    rw [hm]
    have hn : (headsInput).n = (Query.packingProblem query k hg).n := by rfl
    rw [hn, one_mul]
    exact QueryTargetMetadata.count_modulus query k lengths hg
  exact run_space_of_outputs m ht hd M cache half e hp a hscratch hframe hnodes
    hQ (order_of_model query k lengths hg m hm) hfield
    (by rw [hm]; exact Query.ring_exponent (query.input k) lengths hg)
    (NodeConcrete.specTarget factor H high) outputs hlen hstream houtputs hdegree
    _ 1 (headsInput).n (by simpa using hcount) hlarge hconstant B S ha
    hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize
    ((DisjointReuse.binaryNat_length_le hcount).trans hambient)

theorem query_run_space_with_full_frame (H : Finset (Fin (headsInput).n)) (high : H → Bool)
    (hwidth : ∀ clause ∈ source, clause.length ≤ k)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (outputs : List (List Bool)) (hlen : outputs.length = m.val 21)
    (hstream : a.stacks 863 = outputs.flatten)
    (houtputs : ∀ i : Fin (m.val 21),
      ∃ codes : List (Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
        codes.length = m.val 42 ∧
        codes.map (RingProgram.modelRing (m.val 33) ht hd
          (IrreducibleSearch.data hd) M cache).decode = List.ofFn
          (Truncated.ofPolynomial (m.val 42)
            ((NodeConcrete.specTarget factor H high).comp (X + C
              ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
                (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)))))).coeff ∧
        outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten)
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hambient : (headsInput).n + 1 ≤ B) :
    let count := NodeSemantics.ternaryFixedHighCount H high
      (NodeConcrete.sourceHashes factor) (factor).marked (factor).markedClause
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧ out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 896, i ∈ retainedPorts → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  dsimp only
  have hQ : 0 < m.val 21 := by
    rw [hm, numeric_Q]
    have hh := hg.2.2.2.2.2.2.1
    omega
  have hfield : m.val 21 < 3^(m.val 34) := by
    rw [hm, numeric_Q]
    exact numeric_field query k lengths hg
  have hdegree : (NodeConcrete.specTarget factor H high).natDegree < m.val 21 * m.val 42 := by
    subst m
    exact QueryTargetMetadata.actual_target_degree_executed query hv k hg
      first tail node lengths words hc M cache half e hp source hsource hwidth H high
  have hconstant := QueryTargetMetadata.native_count headsInput m ht hd words hc
    M cache half e hp (field_of_model query k lengths hg m hm) query hv (m.val 42)
    (order_of_model query k lengths hg m hm) source hsource H high
  have hcount := QueryTargetMetadata.native_count_le headsInput m ht hd words hc
    M cache half e hp (field_of_model query k lengths hg m hm) query hv (m.val 42)
    (order_of_model query k lengths hg m hm) source hsource H high
  have hlarge : 1 * 2^(headsInput).n < 3^(m.val 33) := by
    rw [hm]
    have hn : (headsInput).n = (Query.packingProblem query k hg).n := by rfl
    rw [hn, one_mul]
    exact QueryTargetMetadata.count_modulus query k lengths hg
  exact run_space_of_outputs_with_full_frame m ht hd M cache half e hp a hscratch hframe hnodes
    hQ (order_of_model query k lengths hg m hm) hfield
    (by rw [hm]; exact Query.ring_exponent (query.input k) lengths hg)
    (NodeConcrete.specTarget factor H high) outputs hlen hstream houtputs hdegree
    _ 1 (headsInput).n (by simpa using hcount) hlarge hconstant B S ha
    hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize
    ((DisjointReuse.binaryNat_length_le hcount).trans hambient)

end ActualQuery

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction
