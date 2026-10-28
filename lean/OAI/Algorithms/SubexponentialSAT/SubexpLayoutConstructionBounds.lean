import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutFactorBounds

namespace OAI.Algorithms

/-! A fixed polynomial bound for the actual raw layout construction.  The
only size inputs are the retained input words, represented parameters, and
the number `p^k` of possible assignments to at most `k` scope coordinates. -/

namespace SubexponentialSAT.SubexpLayoutConstructionBounds

open SubexpLayoutConstruction

def sourceSize (x : Inputs) (p k : ℕ) : ℕ :=
  SubexpLayoutRawPreparation.inputMass x + variableCount x +
    CounterPrograms.value x.counts.ell + dimension x + p + p ^ k + k + 1

structure InputSizes (x : Inputs) (p k S : ℕ) : Prop where
  mass : SubexpLayoutRawPreparation.inputMass x ≤ S
  variableCount_le : variableCount x ≤ S
  ell : CounterPrograms.value x.counts.ell ≤ S
  dimension : SubexpLayoutConstruction.dimension x ≤ S
  modulus : p ≤ S
  assignments : p ^ k ≤ S
  width : k ≤ S

theorem sourceSize_spec (x : Inputs) (p k : ℕ) : InputSizes x p k (sourceSize x p k) := by
  constructor <;> unfold sourceSize <;> omega

theorem sourceSize_pos (x : Inputs) (p k : ℕ) : 1 ≤ sourceSize x p k := by
  unfold sourceSize
  omega

def conversionBound (S : ℕ) := 32 * (S + 1) * (S + 1)
def unaryCopyBound (S : ℕ) := 7 * S + 5 + conversionBound S
def mastersBound (S : ℕ) :=
  unaryCopyBound S + unaryCopyBound S + unaryCopyBound S +
    (S * (7 * S + 14) + 10) + (2 * S + 3) +
    (7 * S + 5) + (7 * S + 5) + (7 * S + 5)
def unaryFamilyBound (S : ℕ) :=
  conversionBound S + conversionBound S + 3 * (S + S) + 6 +
    200 * (S + S + 1) ^ 2 + 2 * S + 2 * S + 8 +
    400 * (S + S + 1) ^ 2 * (4 * S + 2)
def rawPreparationBound (S : ℕ) := 5000 * (S + unaryFamilyBound S + mastersBound S + 1)
def prefixScopeStreamBound (S : ℕ) := 1 + (2 * (2 * S + 3) + 2) * S
def clauseScopeStreamBound (S : ℕ) := 1 + (2 * scopeBytesBound S + 2) * S
def familyBound (S : ℕ) :=
  (callbackBound S + 17) * (S + 1) +
    16 * (3 * scopeBytesBound S + 2 * prefixScopeStreamBound S + clauseScopeStreamBound S) + 32
def constructionEnvelope (S : ℕ) := rawPreparationBound S + familyBound S + 3

def coefficient : ℕ := 1000000000000
def degree : ℕ := 5
def uniformBound (S : ℕ) := coefficient * S ^ degree

theorem envelope_le (S : ℕ) (hS : 1 ≤ S) : constructionEnvelope S ≤ uniformBound S := by
  have h0 : 1 ≤ S ^ 5 := by simpa using Nat.pow_le_pow_right hS (show 0 ≤ 5 by decide)
  have h1 : S ≤ S ^ 5 := by simpa using Nat.pow_le_pow_right hS (show 1 ≤ 5 by decide)
  have h2 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  unfold constructionEnvelope uniformBound coefficient degree rawPreparationBound
    unaryFamilyBound mastersBound unaryCopyBound conversionBound familyBound
    callbackBound unitBound enumerationBound fieldCallbackBound candidateBound
    countScopeBound scopeProgramBound scopeCallbackBound literalBound
    fuelWidthBound prefixScopeStreamBound clauseScopeStreamBound scopeBytesBound
    mappedScopeBytesBound clauseBytesBound SubexpLiteralChunkProgram.budget
    SubexpFactorCountSetup.budget SubexpFactorCountSetup.countBudget
  ring_nf
  omega

theorem monotone_uniformBound : Monotone uniformBound := by
  intro S T h
  exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

theorem input_word_lengths (x : Inputs) {p k S : ℕ} (h : InputSizes x p k S) :
    x.counts.n.length ≤ S ∧ x.counts.ell.length ≤ S ∧
      x.counts.modulus.length ≤ S ∧ x.counts.dimension.length ≤ S ∧ x.leaf.length ≤ S := by
  have hm := h.mass
  unfold SubexpLayoutRawPreparation.inputMass at hm
  omega

theorem conversion_le (bits : Word) (S : ℕ) (hv : CounterPrograms.value bits ≤ S)
    (hl : bits.length ≤ S) : CounterConversions.runtimeBound bits ≤ conversionBound S := by
  unfold CounterConversions.runtimeBound conversionBound
  gcongr

theorem unary_copy_le (bits : Word) (S : ℕ) (hv : CounterPrograms.value bits ≤ S)
    (hl : bits.length ≤ S) : SubexpClauseMastersProgram.unaryCopyBound bits ≤ unaryCopyBound S := by
  have hc := conversion_le bits S hv hl
  unfold SubexpClauseMastersProgram.unaryCopyBound unaryCopyBound
  gcongr

theorem raw_preparation_le (x : Inputs) {p k S : ℕ} (h : InputSizes x p k S)
    (hp : BinaryArithmetic.toNat x.counts.modulus = p)
    (hell : 0 < CounterPrograms.value x.counts.ell) :
    SubexpLayoutRawPreparation.runtimeBound x ≤ rawPreparationBound S := by
  obtain ⟨hnw, hew, hpw, hdw, _⟩ := input_word_lengths x h
  have hn : CounterPrograms.value x.counts.n ≤ S := h.variableCount_le
  have hd : CounterPrograms.value x.counts.dimension ≤ S := h.dimension
  have he := h.ell
  have hvp : CounterPrograms.value x.counts.modulus = p := by
    simpa only [CounterPrograms.value_eq_toNat] using hp
  have hcn := conversion_le x.counts.n S hn hnw
  have hce := conversion_le x.counts.ell S he hew
  have hu := SubexpUnaryFamily.runtimeBound_polynomial
    x.counts.n x.counts.ell x.counts.modulus hell
  have hucap : SubexpUnaryFamily.runtimeBound x.counts.n x.counts.ell x.counts.modulus ≤
      unaryFamilyBound S := by
    apply hu.trans
    unfold SubexpChunkDescriptorInput.runtimeBound unaryFamilyBound
    rw [hvp]
    gcongr
    exact h.modulus
  have hun := unary_copy_le x.counts.n S hn hnw
  have hue := unary_copy_le x.counts.ell S he hew
  have hud := unary_copy_le x.counts.dimension S hd hdw
  have hmaster : SubexpClauseMastersProgram.workBound x.counts ≤ mastersBound S := by
    unfold SubexpClauseMastersProgram.workBound mastersBound
    gcongr
  unfold SubexpLayoutRawPreparation.runtimeBound rawPreparationBound
  gcongr
  exact h.mass

theorem length_encodeList_append_le {α : Type*} (enc : α → Word) (xs ys : List α) :
    (Encoding.encodeList enc (xs ++ ys)).length ≤
      (Encoding.encodeList enc xs).length + (Encoding.encodeList enc ys).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, Encoding.length_encodeList_cons]
      omega

theorem prefix_lengths_le (x : Inputs) {p k S : ℕ} (h : InputSizes x p k S)
    (hp : BinaryArithmetic.toNat x.counts.modulus = p)
    (hell : 0 < CounterPrograms.value x.counts.ell) :
    (Encoding.encodeList id (prefixTables x)).length ≤ scopeBytesBound S ∧
      (Encoding.encodeList id (prefixScopes x)).length ≤ prefixScopeStreamBound S := by
  have hcount : ChunkPartition.count (variableCount x) (CounterPrograms.value x.counts.ell) ≤ S := by
    apply le_trans _ h.variableCount_le
    exact (ChunkPartition.count_le_iff hell).mpr (Nat.le_mul_of_pos_right _ hell)
  have hvp : CounterPrograms.value x.counts.modulus = p := by
    simpa only [CounterPrograms.value_eq_toNat] using hp
  constructor
  · unfold prefixTables
    rw [SubexpUnaryFamily.chunkTables_encoding_length, hvp]
    unfold scopeBytesBound
    have hpS := h.modulus
    calc
      (2 * p + 2) * _ + 1 ≤ (2 * S + 2) * S + 1 := by gcongr
      _ = _ := by omega
  · have hs : ∀ bits ∈ prefixScopes x, bits.length ≤ 2 * S + 3 := by
      intro bits hb
      obtain ⟨scope, hs, rfl⟩ := List.mem_map.mp hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
      have hjlt := (List.mem_range'_1.mp hj).2
      have hjs : j + 1 ≤ S :=
        (Nat.succ_le_of_lt (by simpa only [Nat.zero_add] using hjlt)).trans hcount
      change (Encoding.encodeList Encoding.encodeNat [j]).length ≤ 2 * S + 3
      simp only [Encoding.length_encodeList_cons, Encoding.length_encodeList_nil,
        Encoding.length_encodeNat]
      simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 hjs) 3
    have hl : (prefixScopes x).length ≤ S := by
      simpa only [prefixScopes, List.length_map, List.length_range'] using hcount
    have he := Encoding.length_encodeList_upper id (prefixScopes x) (2 * S + 3) hs
    exact he.trans (by unfold prefixScopeStreamBound; gcongr)

theorem family_budget_le (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (G : List (List (SAT.Literal (Fin (variableCount x))))) {p k S : ℕ}
    (h : InputSizes x p k S) (hp : BinaryArithmetic.toNat x.counts.modulus = p)
    (hsource : x.leaf = Encoding.encodeList SubexpClauseRowProgram.clauseBytes G)
    (hwidth : ∀ ls ∈ G, ls.length ≤ k) :
    SubexpClauseFamilyProgram.budget (familyInputs x) hv G
      (prefixTables x) (prefixScopes x) ≤ familyBound S := by
  obtain ⟨_, hew, hpw, _, hleaf⟩ := input_word_lengths x h
  have hell : 0 < CounterPrograms.value x.counts.ell := by
    simpa only [familyInputs, CounterPrograms.value_eq_toNat] using hv.ell_pos
  have hpos : 1 ≤ p := by
    have hh := hv.modulus_pos
    change 0 < BinaryArithmetic.toNat x.counts.modulus at hh
    omega
  have hcount : G.length ≤ S := by
    have hg := Encoding.length_encodeList_lower SubexpClauseRowProgram.clauseBytes G
    rw [← hsource] at hg
    omega
  have hrow (ls : List (SAT.Literal (Fin (variableCount x)))) (hls : ls ∈ G) :
      BinaryArithmetic.toNat (familyInputs x).modulus ^
        (SubexpClauseFamilyCallback.scope (familyInputs x) hv ls).length ≤ S := by
    have hs := (SubexpClauseFamilyCallback.scope_length_le (familyInputs x) hv ls).trans
      (hwidth ls hls)
    change BinaryArithmetic.toNat x.counts.modulus ^ _ ≤ S
    rw [hp]
    exact (Nat.pow_le_pow_right hpos hs).trans h.assignments
  have hcallback : ∀ ls ∈ G,
      SubexpClauseFamilyCallback.callbackCost (familyInputs x) hv ls ≤ callbackBound S := by
    intro ls hls
    apply callback_cost_le (familyInputs x) hv ls S hpw hew
    · simpa only [familyInputs, SubexpClauseMastersProgram.unary, List.length_replicate] using h.ell
    · exact h.dimension
    · exact h.variableCount_le
    · exact (hwidth ls hls).trans h.width
    · exact hrow ls hls
  have hscan := SubexpClauseFamilyProgram.scanCost_le (familyInputs x) hv G
    (callbackBound S) hcallback
  rw [← hsource] at hscan
  have hscan' : SubexpClauseFamilyProgram.scanCost (familyInputs x) hv G ≤
      (callbackBound S + 17) * (S + 1) := hscan.trans (by gcongr)
  have ht : (Encoding.encodeList id (SubexpClauseFamilyProgram.tables (familyInputs x) hv G)).length ≤
      scopeBytesBound S := by
    have hh := Encoding.length_encodeList_upper id
      (SubexpClauseFamilyProgram.tables (familyInputs x) hv G) S (by
        intro bits hb
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hb
        change (SubexpClauseFamilyCallback.table (familyInputs x) hv ls).length ≤ S
        rw [SubexpClauseFamilyCallback.table_length]
        exact hrow ls hls)
    simp only [SubexpClauseFamilyProgram.tables, List.length_map] at hh
    exact hh.trans (by unfold scopeBytesBound; gcongr)
  have hs : (Encoding.encodeList id (SubexpClauseFamilyProgram.scopes (familyInputs x) G)).length ≤
      clauseScopeStreamBound S := by
    have hh := Encoding.length_encodeList_upper id
      (SubexpClauseFamilyProgram.scopes (familyInputs x) G) (scopeBytesBound S) (by
        intro bits hb
        obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hb
        change (SubexpClauseFamilyCallback.scopeBytes (familyInputs x) ls).length ≤ scopeBytesBound S
        have hl := (hwidth ls hls).trans h.width
        have hd := h.dimension
        exact (SubexpClauseFamilyCallback.scopeBytes_length_le (familyInputs x) hv ls).trans
          (by unfold scopeBytesBound; gcongr))
    simp only [SubexpClauseFamilyProgram.scopes, List.length_map] at hh
    exact hh.trans (by unfold clauseScopeStreamBound; gcongr)
  obtain ⟨hpt, hps⟩ := prefix_lengths_le x h hp hell
  have hct := length_encodeList_append_le id (prefixTables x)
    (SubexpClauseFamilyProgram.tables (familyInputs x) hv G)
  have hcs := length_encodeList_append_le id (prefixScopes x)
    (SubexpClauseFamilyProgram.scopes (familyInputs x) G)
  rw [SubexpClauseFamilyProgram.budget_eq]
  unfold familyBound
  omega

/-- The actual raw construction bound has a fixed polynomial envelope.
No generated table, scope, or intermediate running-time bound is assumed. -/
theorem runtimeBound_le (x : Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (familyInputs x) (dimension x) (variableCount x))
    (G : List (List (SAT.Literal (Fin (variableCount x))))) (p k : ℕ)
    (hmod : BinaryArithmetic.toNat x.counts.modulus = p)
    (hsource : x.leaf = Encoding.encodeList SubexpClauseRowProgram.clauseBytes G)
    (hwidth : ∀ ls ∈ G, ls.length ≤ k) :
    SubexpLayoutConstruction.runtimeBound x hv G ≤ uniformBound (sourceSize x p k) := by
  have h := sourceSize_spec x p k
  have hell : 0 < CounterPrograms.value x.counts.ell := by
    simpa only [familyInputs, CounterPrograms.value_eq_toNat] using hv.ell_pos
  have hr := raw_preparation_le x h hmod hell
  have hf := family_budget_le x hv G h hmod hsource hwidth
  apply le_trans _ (envelope_le (sourceSize x p k) (sourceSize_pos x p k))
  unfold SubexpLayoutConstruction.runtimeBound constructionEnvelope
  omega

end SubexponentialSAT.SubexpLayoutConstructionBounds

end OAI.Algorithms
