import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingQueryMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecBounds

/-! The polynomial reconstructed by the native query is the target of its
actual generated ternary ring and idempotent code. Its constant term is the
exact marked or unmarked count; the executed parameter bank supplies both
the interpolation budget and sufficient precision. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram
open LeafProgram.PreparedSource LeafProgram.NodeConcrete

attribute [local irreducible] Execute.guardedModel

section Native

variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < (m).val 33) (hd : 0 < (m).val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (s).height
      (LeafHeadSetupProgram.unary (s).R) (s).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((m).val 33))
    (cache : RingProgram.ScalarCache 3 ((m).val 33))
    (half : RingProgram.ScalarCode 3 ((m).val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (s).Q < 3 ^ ((m).val 34))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin (s).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  hfield q hv J hJ source hsource

/-- The actual producer's inverse of two makes the generated idempotent
readout an exact count in the represented ring. -/
theorem native_count (H : Finset (Fin (s).n)) (high : H → Bool) :
    (specTarget spec H high).eval 0 =
      (NodeSemantics.ternaryFixedHighCount H high (sourceHashes spec)
        (spec).marked (spec).markedClause : (spec).p.model.O (spec).p.t) :=
  specTarget_count spec (generatedCode hp).modulus (generatedCode hp).cache
    (generatedCode hp).half rfl (generatedCode hp).inverse H high

/-- A single marked query also counts a subset of the ambient assignments.
No clause multiplicity or positivity assumption is needed for this bound. -/
theorem native_count_le (H : Finset (Fin (s).n)) (high : H → Bool) :
    NodeSemantics.ternaryFixedHighCount H high (sourceHashes spec)
      (spec).marked (spec).markedClause ≤ 2 ^ (s).n := by
  simpa only [one_mul] using specTarget_count_bound spec H high 1 le_rfl

/-- This local degree adapter uses the original source rows without changing
their multiplicity. The actual frontend discharges its budget below. -/
theorem native_degree_of_budget (H : Finset (Fin (s).n)) (high : H → Bool)
    (k factors : ℕ) (hwidth : ∀ c ∈ source, c.length ≤ k)
    (hfactors : q.rows.length ≤ factors)
    (hbudget : k * (s).R * (2 * factors + 3 * ((m).val 33 - 1) + 1) < (s).Q * J) :
    (specTarget spec H high).natDegree < (s).Q * J := by
  apply specTarget_degree_of_budget spec H high k factors hwidth
  · change (castRows (congrArg List.length hsource) q.rows).length ≤ factors
    rw [castRows_length]
    exact hfactors
  · exact hbudget

end Native

/-- The actual frontend includes every original row and any marked or neutral
factor in its measured factor budget. -/
theorem rows_le_input_factors (q : LeafQueryFrontend.Query) (k : ℕ) :
    q.rows.length ≤ (q.input k).factors := by
  change q.rows.length ≤ q.scopeRows.length +
    (LeafQueryFrontend.totals q.scopeRows q.forward).uncovered
  rw [LeafQueryFrontend.Query.scopeRows, HashScopeProgram.Complete.scopes_length]
  omega

theorem numeric_precision (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    (numeric q k lengths).val 33 =
      precision (BinaryArithmetic.toNat q.ambient) (BinaryArithmetic.toNat q.modulus) :=
  numeric_t q k lengths hg

theorem ambient_lt_precision (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    (Query.packingProblem q k hg).n < (numeric q k lengths).val 33 := by
  rw [numeric_precision q k lengths hg]
  change BinaryArithmetic.toNat q.ambient <
    precision (BinaryArithmetic.toNat q.ambient) (BinaryArithmetic.toNat q.modulus)
  unfold precision
  omega

theorem count_modulus (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    2 ^ (Query.packingProblem q k hg).n < 3 ^ (numeric q k lengths).val 33 :=
  (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 3)
      (ambient_lt_precision q k lengths hg))

theorem numeric_order_pos (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    0 < (numeric q k lengths).val 42 := by
  rw [numeric_J q k lengths hg]
  exact produce_J_pos _

section Addressed

variable (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ)
    (hg : Guard (q.input k))
    (first : MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q) (lengths : Fin 8 → ℕ)

local notation "s" => heads q k hg first tail node
local notation "m" => numeric q k lengths
local notation "ht" => Query.ring_precision_pos (q.input k) lengths hg
local notation "hd" => Query.ring_degree_pos (q.input k) lengths hg

/-- The executed jet order is strictly large enough for the actual target's
source width, full factor budget, and ambient precision. -/
theorem actual_degree_budget :
    k * (s).R * (2 * (q.input k).factors + 3 * ((m).val 33 - 1) + 1) <
      (s).Q * (m).val 42 := by
  rw [numeric_t q k lengths hg, numeric_J q k lengths hg]
  exact guard_hermite (q.input k) hg

variable (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads q k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads q k hg first tail node).R)
      (heads q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((numeric q k lengths).val 33))
    (cache : RingProgram.ScalarCache 3 ((numeric q k lengths).val 33))
    (half : RingProgram.ScalarCode 3 ((numeric q k lengths).val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (numeric q k lengths)
      (Query.ring_degree_pos (q.input k) lengths hg) M cache half e)
    (source : List (List (SAT.Literal (Fin (heads q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  (numeric_field q k lengths hg) q hv (Circuit.Model.val m 42)
  (numeric_order_pos q k lengths hg) source hsource

theorem actual_target_degree (hwidth : ∀ c ∈ source, c.length ≤ k)
    (H : Finset (Fin (s).n)) (high : H → Bool) :
    (specTarget spec H high).natDegree < (s).Q * (m).val 42 :=
  native_degree_of_budget s m ht hd words hc M cache half e hp
    (numeric_field q k lengths hg) q hv ((m).val 42)
    (numeric_order_pos q k lengths hg) source hsource H high k (q.input k).factors
    hwidth (rows_le_input_factors q k)
    (actual_degree_budget q k hg first tail node lengths)

theorem actual_target_degree_executed (hwidth : ∀ c ∈ source, c.length ≤ k)
    (H : Finset (Fin (s).n)) (high : H → Bool) :
    (specTarget spec H high).natDegree < (m).val 21 * (m).val 42 := by
  rw [← RingNodeMetadata.actual_heads_node_count q k hg first tail node lengths]
  exact actual_target_degree q hv k hg first tail node lengths words hc M cache half e hp
    source hsource hwidth H high

/-- Changing the interpolation node and its actually produced head cache
leaves the reconstructed source target identical. -/
theorem actual_target_independent
    (node' : Fin (Query.packingProblem q k hg).Q) (words' : List (List Bool))
    (hc' : LeafHeadSetupProgram.CacheCorrect
      (heads q k hg first tail node').height
      (LeafHeadSetupProgram.unary (heads q k hg first tail node').R)
      (heads q k hg first tail node').width words')
    (H : Finset (Fin (s).n)) (high : H → Bool) :
    specTarget spec H high =
      specTarget (nativeSpecOfInputs (heads q k hg first tail node') m ht hd words' hc'
        M cache half e hp (numeric_field q k lengths hg) q hv ((m).val 42)
        (numeric_order_pos q k lengths hg) source hsource) H high := by
  rfl

end Addressed

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata
