import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSelected
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcreteEmbedding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcreteScoped
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteBaseline

/-! Exact source jets and decoded native coefficient words for reconstruction.
The optional marked factor is a violation query, and all free assignments remain. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open scoped BigOperators
open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open LeafProgram LeafProgram.NodeSemantics
open IdempotentApplyProgram.Steps (Context)

section ResidualFactors

variable {V R : Type*} [DecidableEq V] [CommRing R]
  {p t n d : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Specializing an embedded free-variable jet only reads the correction bits
on the image. In particular, the chosen high-coordinate correction bits cannot
change the dense value. -/
theorem specializeDense_jet_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (t J : ℕ) (ambient : W → Bool) (free : V → Bool)
    (hfree : ∀ v, ambient (e v) = free v) (f : Squarefree.Jet V R) :
    QueryEvaluation.specializeDense t J ambient (ResidualEmbedding.jet e f) =
      QueryEvaluation.specializeDense t J free f := by
  change Dense.ofPolynomial t J (Moments.jetEval (Squarefree.boolValue ambient)
    (Squarefree.boolValue_idempotent ambient) (ResidualEmbedding.jet e f)) =
      Dense.ofPolynomial t J (Moments.jetEval (Squarefree.boolValue free)
        (Squarefree.boolValue_idempotent free) f)
  apply congrArg (Dense.ofPolynomial t J)
  rw [ResidualEmbedding.eval_jet]
  have hv : (fun v => (Squarefree.boolValue ambient (e v) : R)) = Squarefree.boolValue free := by
    funext v
    simp only [Squarefree.boolValue, hfree]
  simp only [hv]

/-- Evaluation is required only at literals actually read by the selected ID.
The formal variable type may be the complement of the fixed high coordinates. -/
theorem residualValue_eval_scoped (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (jet : ℕ → Fin n → Squarefree.Jet V R)
    (path : ℕ → Fin n → R[X]) (x : V → R) (hx : ∀ v, x v * x v = x v)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ)
    (hhash : ∀ (hi : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      Moments.jetEval x hx (jet id l.variable) = C (path id l.variable))
    (hmark : marked = true → id = hashes.length → ∀ l ∈ clause,
      Moments.jetEval x hx (jet id l.variable) = C (path id l.variable)) :
    Moments.jetEval x hx
      (AssignmentConcrete.residualValue ctx scalar basis code jet hashes marked clause id) =
      selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path id := by
  unfold AssignmentConcrete.residualValue selectedExpression
  simp only [List.length_map]
  by_cases hi : id < hashes.length
  · simp only [dite_eq_left hi]
    apply indicatorJet_eval _ _ _ x hx
    simp only [hashPath, Fin.getElem_fin, List.getElem_map]
    apply AssignmentConcrete.eval_source_row_scoped (jet id) (path id) x hx
    intro term ht l hl
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    exact hhash hi w hw l hl
  · simp only [dite_eq_right hi]
    by_cases hm : (marked && decide (id = hashes.length)) = true
    · simp only [ite_eq_left hm]
      have hp : marked = true ∧ id = hashes.length := by simpa using hm
      exact AssignmentConcrete.eval_source_clause_scoped
        (jet id) (path id) x hx clause (hmark hp.1 hp.2)
    · simp only [ite_eq_right hm, map_one]

theorem residualValue_eval_at (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (jet : ℕ → Fin n → Squarefree.Jet V R)
    (path : ℕ → Fin n → R[X]) (x : V → R) (hx : ∀ v, x v * x v = x v)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ)
    (hjet : ∀ v, Moments.jetEval x hx (jet id v) = C (path id v)) :
    Moments.jetEval x hx
      (AssignmentConcrete.residualValue ctx scalar basis code jet hashes marked clause id) =
      selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path id := by
  exact residualValue_eval_scoped ctx scalar basis code jet path x hx hashes marked clause id
    (fun _ _ _ _ _ => hjet _) (fun _ _ _ _ => hjet _)

/-- The original canonical residual-factor product specializes to the actual
selected source expressions, with the same shared marker and Taylor cutoffs. -/
theorem residualProduct_specializeDense (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (jet : ℕ → Fin n → Squarefree.Jet V R)
    (path : ℕ → Fin n → R[X]) (x : V → Bool)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ) (J : ℕ)
    (hhash : ∀ id ∈ ids, ∀ (hi : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
        (jet id l.variable) = C (path id l.variable))
    (hmark : marked = true → ∀ id ∈ ids, id = hashes.length → ∀ l ∈ clause,
      Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
        (jet id l.variable) = C (path id l.variable)) :
    QueryEvaluation.specializeDense t J x (Squarefree.canonical t J
      ((ids.map (AssignmentConcrete.residualValue ctx scalar basis code
        jet hashes marked clause)).prod)) =
      Dense.ofPolynomial t J ((ids.map (selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path)).prod) := by
  rw [specializeDense_canonical]
  change Dense.ofPolynomial t J (Moments.jetEval (Squarefree.boolValue x)
    (Squarefree.boolValue_idempotent x) _) = _
  rw [map_list_prod]
  apply congrArg (Dense.ofPolynomial t J)
  apply congrArg List.prod
  rw [List.map_map]
  apply List.map_congr_left
  intro id hid
  exact residualValue_eval_scoped ctx scalar basis code jet path
    (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x) hashes marked clause id
    (hhash id hid) (fun hm he => hmark hm id hid he)

end ResidualFactors



section SourceJets

variable {R G : Type*} [CommRing R] [Fintype G] [DecidableEq G] {n : ℕ}

/-- Summing the actual shifted colored expressions produces every retained
coefficient of the original fixed-high source target. -/
theorem colored_target_dense_shift (H : Finset (Fin n)) (t J : ℕ)
    (digits : Fin t → R[X]) (hashes : List (SparseRow (Fin n) R))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → Fin n → R[X]) (theta : R)
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i ∈ ids)
    (hm : marked = true → hashes.length ∈ ids) (color : ℕ → G) :
    Dense.readout (∑ x : ResidualEmbedding.Free H → Bool, ∏ g,
      Dense.ofPolynomial t J (((ids.filter (fun i => color i = g)).map
        (selectedExpression t digits hashes marked clause
          (fun j v => shift theta (path x j v)))).prod)) =
      Truncated.ofPolynomial J ((target H t digits hashes marked clause path).comp
        (X + C theta)) := by
  rw [map_sum]
  simp_rw [QueryEvaluation.colored_selected_dense_shift t J digits hashes marked clause
    _ theta ids hn hh hm color]
  rw [target, Polynomial.sum_comp]
  exact (map_sum (Truncated.ofPolynomialHom J) _ _).symm

end SourceJets

section NativeReadout

open NodeConcrete MomentsProgram

variable {r Q n d : ℕ} {G : Type*} [Fintype G] [DecidableEq G]

/-- At the actual complete assignment, the stored baseline is the free-row
sum. Only low literal incidences require a source entry; high literals retain
their fixed bit. No supplied jet-evaluation service is used. -/
theorem residualJet_eval_diagonal (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool)
    (hstate : ∀ v : Fin n, (state 145).getD v.val false = HighIncidence.glue H high x v)
    (id : ℕ) (v : Fin n)
    (hpresent : v ∉ H → (v.val, n + id) ∈ q.ps)
    (hzero : ∀ w ∈ H, PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id v.val w = 0) :
    Moments.jetEval (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x)
      (residualJet q.p q.ps q.packing H high q.theta state id v) =
      C (shift (q.p.ops.decode q.theta)
        (branchPath H high (completedRows q.p q.ps q.packing H) x id v)) := by
  by_cases hv : v ∈ H
  · simp only [residualJet, jetEval_ringScalar, branchPath, dite_eq_left hv, shift_C]
  · apply residualJet_eval q.p q.ps q.packing H high q.theta state x id v (hpresent hv)
    intro _
    change (∑ w : Fin n,
      (PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id v.val w).eval
        (q.p.ops.decode q.theta) * HashInput.boolValue ((state 145).getD w.val false)) = _
    simp only [hstate]
    exact sum_free_rows q.p q.ps q.packing H high x id v.val (q.p.ops.decode q.theta) hzero

/-- Diagonal specialization of the actual retained source factor product.
The premises are the physical assignment word and the actual literal scopes,
not evaluator outputs. The native lifting cutoff equals the fixed precision. -/
theorem residual_group_diagonal_dense (q : Factor.Spec r Q n d) (hu : q.u = q.p.t)
    (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool)
    (hstate : ∀ v : Fin n, (state 145).getD v.val false = HighIncidence.glue H high x v)
    (ids : List ℕ)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps) :
    QueryEvaluation.specializeDense q.p.t q.J x
      (Squarefree.canonical q.u q.J ((ids.map
        (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
          (RingBasis.basis (q.p.model.F q.p.t)) q.code
          (residualJet q.p q.ps q.packing H high q.theta state)
          (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)) =
      Dense.ofPolynomial q.p.t q.J ((ids.map
        (selectedExpression q.p.t (codeDigits q.ctx (q.p.model.base q.p.t) q.code)
          (decodedHashes q) q.marked q.markedClause
          (fun id v => shift (q.p.ops.decode q.theta)
            (branchPath H high (completedRows q.p q.ps q.packing H) x id v)))).prod) := by
  rw [hu]
  apply residualProduct_specializeDense q.ctx (q.p.model.base q.p.t)
    (RingBasis.basis (q.p.model.F q.p.t)) q.code
  · intro id hid hi w hw l hl
    exact residualJet_eval_diagonal q H high state x hstate id l.variable
      (hhash id hid hi w hw l hl) (hzero id l.variable.val)
  · intro hm id hid he l hl
    subst id
    exact residualJet_eval_diagonal q H high state x hstate _ l.variable
      (hmark hm hid l hl) (hzero _ l.variable.val)

/-- The actual colored residual products, evaluated at all free assignments,
produce the shifted fixed-high target. Empty groups retain their neutral one,
and additive readout occurs after the complete group product. -/
theorem colored_residual_target_dense_shift (q : Factor.Spec r Q n d)
    (hu : q.u = q.p.t) (H : Finset (Fin n)) (high : H → Bool)
    (state : (ResidualEmbedding.Free H → Bool) → Fin 768 → List Bool)
    (hstate : ∀ x (v : Fin n), (state x 145).getD v.val false = HighIncidence.glue H high x v)
    (ids : List ℕ) (hn : ids.Nodup)
    (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
    (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
    (color : ℕ → G)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps) :
    Dense.readout (∑ x : ResidualEmbedding.Free H → Bool, ∏ g,
      QueryEvaluation.specializeDense q.p.t q.J x
        (Squarefree.canonical q.u q.J (((ids.filter (fun id => color id = g)).map
          (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
            (RingBasis.basis (q.p.model.F q.p.t)) q.code
            (residualJet q.p q.ps q.packing H high q.theta (state x))
            (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod))) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
  have he (x : ResidualEmbedding.Free H → Bool) (g : G) :=
    residual_group_diagonal_dense q hu H high (state x) x (hstate x)
      (ids.filter (fun id => color id = g)) hzero
      (fun id hid => hhash id (List.mem_filter.mp hid).1)
      (fun hmarked hid => hmark hmarked (List.mem_filter.mp hid).1)
  simp_rw [he]
  exact colored_target_dense_shift H q.p.t q.J
    (codeDigits q.ctx (q.p.model.base q.p.t) q.code) (decodedHashes q)
    q.marked q.markedClause (branchPath H high (completedRows q.p q.ps q.packing H))
    (q.p.ops.decode q.theta) ids hn
    (by simpa only [decodedHashes, List.length_map] using hh)
    (by simpa only [decodedHashes, List.length_map] using hm) color

/-- The actual arbitrary-state factor product specializes to its free-variable
source product. The native state supplies the high mask and bits directly;
no legacy assignment context or chosen raw representative is introduced. -/
theorem actualProduct_specializeDense (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (state : Fin 768 → List Bool)
    (hmask : ∀ v : Fin n, (state 702).getD v.val false = decide (v ∈ H))
    (hbits : ∀ v : H, (state 703).getD v.val.val false = high v)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (ids : List ℕ) (ambientU : Fin n → Bool) (U : ResidualEmbedding.Free H → Bool)
    (hU : ∀ v, ambientU v.val = U v) :
    QueryEvaluation.specializeDense q.u q.J ambientU
      (Squarefree.canonical q.u q.J ((ids.map (q.value state)).prod)) =
      QueryEvaluation.specializeDense q.u q.J U
        (Squarefree.canonical q.u q.J ((ids.map
          (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
            (RingBasis.basis (q.p.model.F q.p.t)) q.code
            (residualJet q.p q.ps q.packing H high q.theta state)
            (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)) := by
  have hj (id : ℕ) (v : Fin n) :
      AssignmentConcrete.sourceJets q state id v =
        ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
          (residualJet q.p q.ps q.packing H high q.theta state id v) :=
    factorJet_embedding q.p q.ps q.packing H high q.theta state id v
      (hmask v) (fun hv => hbits ⟨v, hv⟩) (hzero id v.val)
  have he := AssignmentConcrete.canonical_product_embedding (ResidualEmbedding.inclusion H)
    q.ctx (q.p.model.base q.p.t) (RingBasis.basis (q.p.model.F q.p.t)) q.code
    (residualJet q.p q.ps q.packing H high q.theta state)
    (AssignmentConcrete.sourceJets q state) hj
    (AssignmentConcrete.weightedHashes q) q.marked q.markedClause ids
  rw [AssignmentConcrete.value_function]
  exact (congrArg (QueryEvaluation.specializeDense q.u q.J ambientU) he).trans
    (specializeDense_jet_embedding (ResidualEmbedding.inclusion H)
      q.u q.J ambientU U hU _)

/-- Actual native readout words supply all coefficients below J. Only the
retained additive readout is specified, after the complete group products. -/
theorem native_readout_hasJets (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (nodes : Fin Q → RingProgram.Code (RingProgram.ScalarCode 3 q.p.t) d)
    (ids : Fin Q → List ℕ) (hn : ∀ i, (ids i).Nodup)
    (hh : ∀ i j, j < (decodedHashes q).length → j ∈ ids i)
    (hm : q.marked = true → ∀ i, (decodedHashes q).length ∈ ids i)
    (color : Fin Q → ℕ → G)
    (entries : Fin Q → List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hkeys : ∀ i, (Squarefree.Sparse.keys (entries i)).Nodup)
    (zero : RingProgram.Code (RingProgram.ScalarCode 3 q.p.t) d)
    (hz : q.p.ops.decode zero = 0)
    (hvalue : ∀ i,
      Dense.readout (TruncatedRingProgram.rawValue q.p.t q.J q.p.ops.decode (entries i)) =
        Dense.readout (∑ x : ResidualEmbedding.Free H → Bool, ∏ g,
          Dense.ofPolynomial q.p.t q.J (((ids i).filter (fun j => color i j = g)).map
            (selectedExpression q.p.t (codeDigits q.ctx (q.p.model.base q.p.t) q.code)
              (decodedHashes q) q.marked q.markedClause
              (fun j v => shift (q.p.ops.decode (nodes i))
                (branchPath H high (completedRows q.p q.ps q.packing H) x j v)))).prod)) :
    Reconstruction.HasJets q.p.ops nodes q.J
      (fun i => MomentsReadoutProgram.outputCodes 3 q.p.t q.p.modulus q.p.cache
        (entries i) q.p.t zero 0 q.J) (specTarget q H high) := by
  apply Reconstruction.hasJets_of_coefficients
  intro i z hzJ
  have hread := TruncatedRingProgram.readout_codes_dense 3 q.p.t q.p.modulus q.p.cache
    (q.p.model.base q.p.t) (RingBasis.basis (q.p.model.F q.p.t))
    q.p.t q.J (entries i) zero (hkeys i) hz
  change Truncated.ofPolynomial q.J
    (PolynomialAlgorithm.denote ((MomentsReadoutProgram.outputCodes 3 q.p.t
      q.p.modulus q.p.cache (entries i) q.p.t zero 0 q.J).map q.p.ops.decode)) =
    Dense.readout (TruncatedRingProgram.rawValue q.p.t q.J q.p.ops.decode (entries i)) at hread
  rw [hvalue i] at hread
  rw [colored_target_dense_shift H q.p.t q.J
    (codeDigits q.ctx (q.p.model.base q.p.t) q.code) (decodedHashes q)
    q.marked q.markedClause (branchPath H high (completedRows q.p q.ps q.packing H))
    (q.p.ops.decode (nodes i)) (ids i) (hn i) (hh i) (fun h => hm h i) (color i)] at hread
  have hc := congrArg (fun a => a.coeff (⟨z, hzJ⟩ : Fin q.J)) hread
  simpa only [Truncated.coeff_ofPolynomial, specTarget] using hc

end NativeReadout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
