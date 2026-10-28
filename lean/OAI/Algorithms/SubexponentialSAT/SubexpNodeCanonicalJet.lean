import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJetSemantics

namespace OAI.Algorithms

/-! Canonical bytes of the actual node jet. The moment machine starts with
canonical zero cells and every cell replacement is a normalized binary sum.
Consequently its semantic jet determines its complete output bytes. The
canonical byte function below is a specification, not a runtime operation. -/

namespace SubexponentialSAT.SubexpNodeCanonicalJet

noncomputable section

open SubexpLiftRing SubexpQuarticRing SubexpSymbolicCost SubexpCanonicalWords
open SubexpLayoutSpec SubexpSelectedConversions

variable (p D : ℕ) [Fact p.Prime]

/-- The actual lifted ring and the selected quartic ring are the same quotient;
this typed wrapper keeps that identification explicit at serialization boundaries. -/
noncomputable def encodeRing (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (x : SubexpActualRing.Ring p μ) : List Bool :=
  SubexpQuarticEncoding.encodeSelected p μ hμ x

@[simp] theorem encodeRing_length (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (x : SubexpActualRing.Ring p μ) :
    (encodeRing p μ hμ x).length = 4 * μ * (Nat.log 2 p + 1) :=
  SubexpQuarticEncoding.encodeSelected_length p μ hμ x

theorem zero_canonical : CanonicalQuad p (D+1)
    (SubexpCoefficientLookup.zeroCoefficient p (D+1)) := by
  have hz : CanonicalWord p (D+1) (SubexpPreparedQuartic.zeroWord p (D+1)) := by
    change BinaryArithmetic.toNat (List.replicate (baseWidth p (D+1)) false) < p^(D+1)
    have hzero (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false) = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, BinaryArithmetic.toNat_cons,
          BinaryArithmetic.bitVal_false, ih]
    rw [hzero]
    exact pow_pos (Fact.out : p.Prime).pos _
  exact ⟨hz,hz,hz,hz⟩

variable (M : SubexpPreparedQuartic.Modulus p (D+1)) (t z o : QuarticCode p D)
  (slots : List (SymbolicCost.RawIndex D))
  (source : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D (QuarticCode p D)))

theorem step_canonical (xs : List (QuarticCode p D))
    (hx : ∀ x ∈ xs, CanonicalQuad p (D+1) x) (q : SubexpExtractionJobs.Query D) :
    ∀ x ∈ SubexpMomentPhase.step p D M t z o slots source xs q,
      CanonicalQuad p (D+1) x := by
  intro x h
  rcases List.mem_or_eq_of_mem_set h with h | h
  · exact hx x h
  · rw [h]
    exact binaryAdd_canonical p (D+1) M _ _

theorem fold_canonical (qs : List (SubexpExtractionJobs.Query D))
    (xs : List (QuarticCode p D)) (hx : ∀ x ∈ xs, CanonicalQuad p (D+1) x) :
    ∀ x ∈ qs.foldl (SubexpMomentPhase.step p D M t z o slots source) xs,
      CanonicalQuad p (D+1) x := by
  induction qs generalizing xs with
  | nil => exact hx
  | cons q qs ih =>
      exact ih _ (step_canonical p D M t z o slots source xs hx q)

theorem from_zero_canonical (qs : List (SubexpExtractionJobs.Query D)) :
    ∀ x ∈ qs.foldl (SubexpMomentPhase.step p D M t z o slots source)
      (SubexpMomentPhase.zeroCells p D), CanonicalQuad p (D+1) x := by
  apply fold_canonical p D M t z o slots source
  intro x hx
  have he := (List.mem_replicate.mp hx).2
  subst x
  exact zero_canonical p D

theorem word_encode_value (x : Word (baseWidth p (D+1)))
    (hx : CanonicalWord p (D+1) x) : encodeBase p (D+1) (wordValue p (D+1) x) = x.val := by
  have he : encodeWord p (D+1) (wordValue p (D+1) x) = x := by
    apply word_eq_of_value_eq p (D+1) _ x _ hx (wordValue_encodeWord p (D+1) _)
    change BinaryArithmetic.toNat (encodeBase p (D+1) (wordValue p (D+1) x)) < p^(D+1)
    rw [encodeBase_value]
    exact (wordValue p (D+1) x).val_lt
  exact congrArg Subtype.val he

theorem encode_decode (x : QuarticCode p D) (hx : CanonicalQuad p (D+1) x) :
    encodeRing p (D+1) (Nat.succ_pos D)
      (SubexpFactorPacketProvenance.decode p D x) = SubexpFlatAdd.encode x := by
  change SubexpQuarticEncoding.encodeSelected p (D+1) (Nat.succ_pos D)
    (quotientDenote (QuarticSearch.liftedCoefficients p (D+1))
      (x.map (wordValue p (D+1)))) = _
  rw [SubexpQuarticEncoding.encodeSelected,
    SubexpQuarticEncoding.encodeQuotient_quotientDenote]
  simp only [SubexpQuarticEncoding.encodeQuad, Quad.map,
    word_encode_value p D x.c0 hx.1, word_encode_value p D x.c1 hx.2.1,
    word_encode_value p D x.c2 hx.2.2.1, word_encode_value p D x.c3 hx.2.2.2,
    SubexpFlatAdd.encode, SubexpFlatAdd.quadWords, SubexpFlatAdd.flatten,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem bytes_eq_encode (xs : List (QuarticCode p D))
    (hx : ∀ x ∈ xs, CanonicalQuad p (D+1) x) :
    SubexpMomentPhase.cellsBytes p D xs =
      ((xs.map (SubexpFactorPacketProvenance.decode p D)).map
        (encodeRing p (D+1) (Nat.succ_pos D))).flatten := by
  unfold SubexpMomentPhase.cellsBytes
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.flatten_cons]
      rw [encode_decode p D x (hx x (by simp)), ih (fun y hy => hx y (by simp [hy]))]

variable {p D}
  {k Δ r : ℕ} {tau : ℚ} {F : Type*} [Fintype F] [DecidableEq F]
  {pattern : Factor.Pattern (Fin D) F} {params : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) pattern params)
  (table : ∀ e, MvPolynomial {v // v ∈ pattern.scope e} (SubexpActualRing.Ring p (D+1)))

/-- Depends only on the true layout, local factor tables, and node. -/
def canonicalJetBytes (node : Fin params.Q) : List Bool :=
  let A := SubexpExplicitLift.explicitLiftedLayout L (D+1) (Nat.succ_pos D)
  ((List.range D).map fun j =>
    encodeRing p (D+1) (Nat.succ_pos D)
      ((JetCRT.jet (A.theta node) D
        (GlobalPolynomial.rowGlobalPolynomial table A.row (SubexpActualRing.coordinateLift p (D+1)))).coeff j)).flatten

omit [DecidableEq F] in
theorem canonicalJetBytes_length (node : Fin params.Q) :
    (canonicalJetBytes L table node).length = D * (4 * baseWidth p (D+1)) := by
  unfold canonicalJetBytes
  rw [List.length_flatten, List.map_map]
  simp [Function.comp_def]
  left
  unfold baseWidth
  ring

section Concrete

variable {ctx : SubexpMomentSourceProgram.Context}
  (target : Prepared p ctx.dimension) (actual : SubexpNodeJetSemantics.Family p ctx.dimension)
  {arity : F → ℕ} {pattern : Factor.Pattern (Fin ctx.dimension) F}
  {params : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) pattern params)
  (node : Fin params.Q) (enum : EnumerationData L node)
  (source : Prepared p 0) (theta : QuarticCode p ctx.dimension)
  (packetInputs : ∀ e, SubexpFactorPacketProvenance.Input p ctx.dimension p (arity e) params.R)
  (es : List F) (words : F → MulticolorTypes.Word r params.Q)
  (cache : List (List (QuarticCode p ctx.dimension)))

local notation "dim" => ctx.dimension
local notation "decode" => SubexpFactorPacketProvenance.decode p ctx.dimension
local notation "labels" => SubexpLagrangeCacheAlgebra.integerNodes p (ctx.dimension + 1)
local notation "units" => SubexpLagrangeCacheAlgebra.integerNodes_units p (ctx.dimension + 1)

/-- The exact byte output of the actual moment machine is independent of
the generated expression family and caller registers. -/
theorem jet_eq_canonicalJetBytes
    (hnodup : es.Nodup) (hcomplete : ∀ e, e ∈ es)
    (ix : ∀ e, Fin (arity e) ≃ {v // v ∈ pattern.scope e})
    (table : ∀ e, MvPolynomial {v // v ∈ pattern.scope e}
      (SubexpActualRing.Ring p (ctx.dimension + 1)))
    (hcolor : ∀ e, words e node = L.color e node)
    (htable : ∀ e, SubexpTableInterpolation.tablePolynomial labels units
      ((packetInputs e).rows.map (SubexpRepresentedBuilder.mapRow decode)) =
        MvPolynomial.rename (ix e).symm (table e))
    (horigin : ∀ e i w, source.residueRing.decode ((packetInputs e).origins i w) =
      (L.row e (ix e i) w).eval (L.node node))
    (hrow : ∀ e i w,
      (((packetInputs e).sourceRows i w).map (SubexpRowSourceSemantics.denote source)).eval =
        L.row e (ix e i) w)
    (htheta : decode theta =
      (SubexpExplicitLift.explicitLiftedLayout L (dim+1) (Nat.succ_pos dim)).theta node)
    (hcache : ∀ i : Fin p,
      PolynomialAlgorithm.denote ((cache.map (List.map decode)).getD i.val []) =
        TableInterpolation.basis labels units i)
    (hrel : letI : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
      ∀ a : Fin dim → ℕ,
        List.Forall₂ (SubexpSourceReference.BlockRel decode) (actual a)
          (SubexpConcreteSourceProvenance.reference (ctx := ctx)
            L node enum source theta packetInputs es words cache a)) :
    letI : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
    SubexpNodePhaseExecution.jet p dim target.modulus target.reduction target.zero target.one
      (SubexpQueryOrder.visitSlots dim) (SubexpNodeSourceJobs.expression p ctx actual)
      (SubexpQueryOrder.generatedQueries dim) = canonicalJetBytes L table node := by
  let this : One (QuarticCode p ctx.dimension) := ⟨target.one⟩
  have hc := from_zero_canonical p dim target.modulus target.reduction target.zero target.one
    (SubexpQueryOrder.visitSlots dim) (SubexpNodeSourceJobs.expression p ctx actual)
    (SubexpQueryOrder.generatedQueries dim)
  have he := SubexpNodeJetSemantics.cells_eq_layoutJet ctx target actual L node enum source theta
    packetInputs es words cache hnodup hcomplete ix table hcolor htable horigin hrow htheta hcache hrel
  have hcanon : ∀ x ∈ SubexpNodeJetSemantics.cells ctx target actual,
      CanonicalQuad p (dim+1) x := hc
  rw [SubexpNodeJetSemantics.jet_eq_cellsBytes,
    bytes_eq_encode p dim (SubexpNodeJetSemantics.cells ctx target actual) hcanon, he]
  simp only [canonicalJetBytes, List.map_map, Function.comp_def]

end Concrete

end

end SubexponentialSAT.SubexpNodeCanonicalJet

end OAI.Algorithms
