import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsSelected
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingSource

/-! Exact dense semantics of the native selected-factor run after immediate
Boolean specialization. The common lifting marker remains through products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open scoped BigOperators
open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open LeafProgram LeafProgram.NodeSemantics
open IdempotentApplyProgram.Steps (Context)



section SpecializedNativeFactors

variable {R A : Type*} [CommRing R] [CommRing A]
  {p t n d : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- The indicator only uses its scalar coefficients, shared marker, and input.
Thus two coefficient-ring maps agreeing on those data give the same value. -/
theorem indicatorJet_eval_congr
    (F G : Squarefree.Jet (Fin n) R →+* A)
    (hs : F.comp Moments.ringScalar = G.comp Moments.ringScalar)
    (hX : F Polynomial.X = G Polynomial.X)
    (t : ℕ) (digits : Fin t → R[X]) (a b : Squarefree.Jet (Fin n) R)
    (hab : F a = G b) : F (indicatorJet t digits a) = G (indicatorJet t digits b) := by
  unfold indicatorJet
  simp only [map_sum, map_mul, map_pow, Polynomial.hom_eval₂, hs, hX, hab,
    IdempotentProgram.hValue, map_sub, map_one, map_ofNat]

/-- Naturality of the actual selected expression, including marked violations
and neutral IDs, under maps that retain the common lifting marker. -/
theorem selectedValue_eval_congr (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (F G : Squarefree.Jet (Fin n) R →+* A)
    (hs : ∀ c, F (Moments.ringScalar c) = G (Moments.ringScalar c))
    (hX : F Polynomial.X = G Polynomial.X)
    (left right : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hjet : ∀ id v, F (left id v) = G (right id v))
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    F (AssignmentSemantics.selectedValue ctx scalar basis code left hashes marked clause id) =
      G (AssignmentSemantics.selectedValue ctx scalar basis code right hashes marked clause id) := by
  unfold AssignmentSemantics.selectedValue
  by_cases hi : id < hashes.length
  · simp only [dite_eq_left hi, indicatorPolynomial_eq]
    apply indicatorJet_eval_congr F G (RingHom.ext hs) hX
    rw [← rowValue_eq_eval (R := Squarefree.Jet (Fin n) R) scalarJet (left id),
      ← rowValue_eq_eval (R := Squarefree.Jet (Fin n) R) scalarJet (right id),
      LeafProgram.map_rowValue F scalarJet (left id),
      LeafProgram.map_rowValue G scalarJet (right id)]
    simp only [ResidualEmbedding.scalarJet_eq_ringScalar, hs, hjet]
  · simp only [dite_eq_right hi]
    split
    · rw [← clauseValue_eq_eval (R := Squarefree.Jet (Fin n) R) (left id),
        ← clauseValue_eq_eval (R := Squarefree.Jet (Fin n) R) (right id),
        LeafProgram.map_clauseValue F (left id), LeafProgram.map_clauseValue G (right id)]
      simp only [hjet]
    · simp only [map_one]

/-- The actual source expression computed from already-specialized incidence
jets has exactly the bounded dense value of the unspecialized expression. -/
theorem selectedValue_specialized_dense (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (U : Fin n → Bool) (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id u J : ℕ) :
    TruncatedRingProgram.jetProjection u J
      (AssignmentSemantics.selectedValue ctx scalar basis code
        (fun id v => Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
          (Squarefree.boolValue_idempotent U) (jet id v))) hashes marked clause id) =
      QueryEvaluation.specializeDense u J U
        (AssignmentSemantics.selectedValue ctx scalar basis code jet hashes marked clause id) := by
  apply selectedValue_eval_congr ctx scalar basis code
  · intro c
    change TruncatedRingProgram.jetProjection u J (Moments.ringScalar c) =
      Dense.ofPolynomial u J (Moments.jetEval (Squarefree.boolValue U)
        (Squarefree.boolValue_idempotent U) (Moments.ringScalar c))
    rw [jetEval_ringScalar]
    rw [Moments.ringScalar_constant, TruncatedRingProgram.jetProjection_jetScalar]
    rfl
  · simp [TruncatedRingProgram.jetProjection, QueryEvaluation.specializeDense,
      Squarefree.evalJet]
  · intro id v
    exact TruncatedRingProgram.jetProjection_jetScalar u J _

/-- One actual selected-factor multiplication extends an arbitrary valid
empty-support accumulator. Both the resulting validity and its dense value
refer to the same native product output. -/
theorem selectedFactor_step_specialized_dense (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k)) * basis k)
    (hd : 0 < d) (hb : basis ⟨0, hd⟩ = 1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (incidence : ℕ → Fin n → AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (hone : NativeSemantics.Good ∅ ctx.u ctx.J one)
    (hseed : NativeSemantics.Good ∅ ctx.u ctx.J seed)
    (hi : ∀ id v, NativeSemantics.Good ∅ ctx.u ctx.J (incidence id v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : NativeSemantics.rawDenote
      (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
      one = Squarefree.canonical ctx.u ctx.J 1)
    (U : Fin n → Bool) (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ)
    (hhash : ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      NativeSemantics.rawDenote
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
        (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J
          (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
            (Squarefree.boolValue_idempotent U) (jet id l.variable))))
    (hmark : marked = true → id = hashes.length → ∀ l ∈ clause,
      NativeSemantics.rawDenote
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
        (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J
          (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
            (Squarefree.boolValue_idempotent U) (jet id l.variable))))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (factor : AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (hfactor : AssignmentSemantics.selectedFactor ctx minus one incidence hashes marked clause
      (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)) id = some factor) :
    let output := MomentsProgram.Product.run p t ctx.modulus ctx.cache ctx.table
      ctx.u ctx.J seed factor []
    NativeSemantics.Good ∅ ctx.u ctx.J output ∧
      TruncatedRingProgram.rawValue ctx.u ctx.J
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis) output =
      TruncatedRingProgram.rawValue ctx.u ctx.J
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis) seed *
      QueryEvaluation.specializeDense ctx.u ctx.J U
        (AssignmentSemantics.selectedValue ctx scalar basis code jet hashes marked clause id) := by
  dsimp only
  have hg := AssignmentSemantics.selectedFactor_good ctx ∅ hu hJ minus one incidence hone hi
    hashes marked clause _ id factor hfactor
  refine ⟨NativeSemantics.product_good p t ctx.modulus ctx.cache ctx.table ∅ ctx.u ctx.J
    seed factor hseed hg, ?_⟩
  rw [TruncatedRingProgram.product_dense p t ctx.modulus ctx.cache scalar basis
    ctx.table htable ctx.u ctx.J seed factor]
  apply congrArg (fun value => TruncatedRingProgram.rawValue ctx.u ctx.J
    (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis) seed * value)
  have hv := AssignmentSemantics.selectedFactor_denote_at ctx scalar basis htable hd hb hu hJ
    ∅ minus one incidence hone hi hminus honeval
    (fun id v => Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
      (Squarefree.boolValue_idempotent U) (jet id v)))
    hashes marked clause id hhash hmark code factor hfactor
  change TruncatedRingProgram.jetProjection ctx.u ctx.J (NativeSemantics.rawDenote _ factor) = _
  rw [hv, TruncatedRingProgram.jetProjection_canonical]
  exact selectedValue_specialized_dense ctx scalar basis code U jet hashes marked clause
    id ctx.u ctx.J

/-- The SAME native selected-run output over empty-support incidence dictionaries
has the specialized dense product value. The incidence denotation premises are
literal-scoped and supplied by the actual specialized producer. -/
theorem selectedRun_specialized_dense (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k)) * basis k)
    (hd : 0 < d) (hb : basis ⟨0, hd⟩ = 1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (incidence : ℕ → Fin n → AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (hone : NativeSemantics.Good ∅ ctx.u ctx.J one)
    (hi : ∀ id v, NativeSemantics.Good ∅ ctx.u ctx.J (incidence id v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : NativeSemantics.rawDenote
      (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
      one = Squarefree.canonical ctx.u ctx.J 1)
    (U : Fin n → Bool) (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ)
    (hhash : ∀ id ∈ ids, ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      NativeSemantics.rawDenote
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
        (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J
          (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
            (Squarefree.boolValue_idempotent U) (jet id l.variable))))
    (hmark : hashes.length ∈ ids → marked = true → ∀ l ∈ clause,
      NativeSemantics.rawDenote
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
        (incidence hashes.length l.variable) = Squarefree.canonical ctx.u ctx.J
          (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
            (Squarefree.boolValue_idempotent U) (jet hashes.length l.variable))))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t)) :
    TruncatedRingProgram.rawValue ctx.u ctx.J
      (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
      (AssignmentSemantics.selectedRun ctx.modulus ctx.cache ctx.table ctx.u ctx.J
        (AssignmentSemantics.selectedFactor ctx minus one incidence hashes marked clause
          (List.ofFn (IdempotentApplyProgram.coefficientTriple t code))) ids one) =
      QueryEvaluation.specializeDense ctx.u ctx.J U (Squarefree.canonical ctx.u ctx.J
        ((ids.map (AssignmentSemantics.selectedValue ctx scalar basis code
          jet hashes marked clause)).prod)) := by
  have hv := AssignmentSemantics.selectedRun_polynomial_selected ctx scalar basis htable
    hd hb hu hJ ∅ minus one incidence hone hi hminus honeval
    (fun id v => Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
      (Squarefree.boolValue_idempotent U) (jet id v)))
    hashes marked clause ids hhash hmark code
  unfold TruncatedRingProgram.rawValue
  change TruncatedRingProgram.jetProjection ctx.u ctx.J (NativeSemantics.rawDenote _ _) = _
  rw [hv, TruncatedRingProgram.jetProjection_canonical, specializeDense_canonical,
    map_list_prod, map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro id _
  exact selectedValue_specialized_dense ctx scalar basis code U jet hashes marked clause
    id ctx.u ctx.J

end SpecializedNativeFactors

section RescanQuery

open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments QueryEvaluation

variable {V G R : Type*} [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [CommRing R]
  {L : G → Type*} [∀ g, DecidableEq (L g)]

/-- The exact dense query in the form tested by the native full-head rescan:
the complete attained key and correction condition guard each contribution.
The shared-marker readout is applied after every group multiplication. -/
theorem grouped_dense_query_rescan (t J : ℕ) (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g)
    (reps : ∀ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g))
    (A : G → (V → Bool) → Squarefree.Jet V R)
    (hadm : ∀ x, Squarefree.Admissible (∏ g, A g x))
    (hlocal : ∀ (U : Finset V) g x z,
      split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      specializeDense t J (fun v => decide (v ∈ U)) (A g x) =
        specializeDense t J (fun v => decide (v ∈ U)) (A g z)) :
    Dense.readout (∑ x, specializeDense t J x (∏ g, A g x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ y : ∀ g, LabelValue label g,
            Dense.readout (∏ g, ∑ a : Head head g → Bool,
              if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
                specializeDense t J (fun v => decide (v ∈ U))
                  (A g (assemble head (Function.update (fun h => (reps y h).val) g a)))
              else 0) := by
  classical
  rw [dense_jet_finite_differences t J (fun x => ∏ g, A g x) hadm]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro U _
  apply congrArg (fun a => ((-1 : ℤ) ^ (E.card - U.card)) • a)
  have hg := HeadEvaluation.restricted_grouping_rescan head label reps E
    (fun g x => specializeDense t J (fun v => decide (v ∈ U)) (A g x)) (hlocal U)
  have hgroup :
      (∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
        specializeDense t J (fun v => decide (v ∈ U)) (∏ g, A g x)) =
      ∑ y : ∀ g, LabelValue label g, ∏ g, ∑ a : Head head g → Bool,
        if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
          specializeDense t J (fun v => decide (v ∈ U))
            (A g (assemble head (Function.update (fun h => (reps y h).val) g a)))
        else 0 := by
    simpa only [Finset.sum_filter, map_prod] using hg
  simpa only [map_sum] using congrArg Dense.readout hgroup

end RescanQuery

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
