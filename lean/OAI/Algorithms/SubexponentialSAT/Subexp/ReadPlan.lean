import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PaddedCompletion
import OAI.Algorithms.SubexponentialSAT.Subexp.NaturalAssignment

namespace OAI.Algorithms

/-!
# Explicit local read plans

Read plans are lists of numeric positions in the explicit seed array. The
machine-facing data are fixed-width one-hot word records and unary indices.
Gathering them in head/slot order reproduces the actual type encoding.
-/

namespace SubexponentialSAT.Subexp.ReadPlan

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment
open SubexponentialSAT.Subexp.AssignmentEnumeration

section Gather

variable {W : Type*}

def gather (default : W) (rows : List W) (plan : List ℕ) : List W :=
  plan.map (fun n => rows.getD n default)

@[simp] theorem gather_length (default : W) (rows : List W) (plan : List ℕ) :
    (gather default rows plan).length = plan.length := by simp [gather]

def unaryPlan (plan : List ℕ) : List (List Bool) :=
  plan.map (fun n => List.replicate n true)

@[simp] theorem unaryPlan_lengths (plan : List ℕ) :
    (unaryPlan plan).map List.length = plan := by
  simp [unaryPlan, List.map_map, Function.comp_def]

theorem getD_map_of_lt {A B : Type*} (f : A → B) (xs : List A)
    (a : A) (b : B) (n : ℕ) (hn : n < xs.length) :
    (xs.map f).getD n b = f (xs.getD n a) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getD_eq_getElem _ _ hn]
  simp

end Gather

section Encoding

variable {r Q Δ : ℕ}

def wordWidth (r Q : ℕ) : ℕ := Q * r

/-- Position first, then color: each letter is a one-hot r-bit record. -/
def encodeWord (w : Word r Q) : List Bool :=
  (List.ofFn fun q : Fin Q => List.ofFn fun c : Fin r => decide (w q = c)).flatten

@[simp] theorem encodeWord_length (w : Word r Q) :
    (encodeWord w).length = wordWidth r Q := by
  simp [encodeWord, wordWidth, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.ofFn_const]

private theorem ofFn_prod {A : Type*} {m n : ℕ} (f : Fin (m * n) → A) :
    List.ofFn f =
      (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n =>
        f (finProdFinEquiv (i, j))).flatten := by
  simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm, Nat.mul_comm]
    using List.ofFn_mul f

/-- Concatenating encoded head and slot words is the existing type encoding. -/
theorem encodeType_eq_words (u : UniversalType r Q Δ) :
    CollisionProgram.encodeType u =
      (List.ofFn fun a : Fin (Δ + 1) =>
        encodeWord (CollisionProgram.registerWord u a)).flatten := by
  calc
    CollisionProgram.encodeType u =
        ((List.ofFn fun a : Fin (Δ + 1) => List.ofFn fun q : Fin Q =>
          List.ofFn fun c : Fin r =>
            decide (CollisionProgram.registerWord u a q = c)).flatten).flatten := by
      unfold CollisionProgram.encodeType
      unfold CollisionProgram.typeWidth
      change List.ofFn (fun j : Fin (((Δ + 1) * Q) * r) =>
        CollisionProgram.codeBit u j) = _
      rw [ofFn_prod (m := (Δ + 1) * Q) (n := r)]
      rw [ofFn_prod (m := Δ + 1) (n := Q)]
      simp only [CollisionProgram.codeBit, Equiv.symm_apply_apply]
    _ = _ := by
      rw [List.flatten_flatten, List.map_ofFn]
      rfl

end Encoding

section VertexPlans

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} (slots : SlotMap P Δ)

def registerCoord (a : Fin (Δ + 1)) : LocalCoord Δ :=
  Fin.cases (.inl ()) Sum.inr a

def readSeed (v : V) (a : Fin (Δ + 1)) : SeedIndex V E Δ :=
  SubexponentialSAT.TypeDistribution.reads P slots v (registerCoord a)

omit [DecidableEq E] in
theorem registerWord_assignmentType (ω : Assignment V E r Q Δ) (v : V)
    (a : Fin (Δ + 1)) :
    CollisionProgram.registerWord (assignmentType P slots ω v) a =
      ω (readSeed P slots v a) := by
  refine Fin.cases ?_ (fun i => ?_) a
  · rfl
  · simp [CollisionProgram.registerWord, registerCoord, readSeed,
      assignmentType, wordTypeEquiv]

/-- Seed-array positions, with the head first and the slots in numeric order. -/
def vertexPlan (vertices : List V) (factors : List E) (v : V) : List ℕ :=
  List.ofFn (fun a : Fin (Δ + 1) =>
    seedCode vertices factors Δ (readSeed P slots v a))

@[simp] theorem vertexPlan_length (vertices : List V) (factors : List E) (v : V) :
    (vertexPlan P slots vertices factors v).length = Δ + 1 := by
  simp [vertexPlan]

theorem vertexPlan_valid (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) (v : V)
    (n : ℕ) (hn : n ∈ vertexPlan P slots vertices factors v) :
    n < (seedIndices vertices factors Δ).length := by
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hn
  simpa only [seedIndices_length] using
    seedCode_lt vertices factors Δ hv he (readSeed P slots v a)

theorem mem_vertexPlan_iff (vertices : List V) (factors : List E) (v : V) (n : ℕ) :
    n ∈ vertexPlan P slots vertices factors v ↔
      n ∈ (readSupport P slots v).image (seedCode vertices factors Δ) := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp h
    apply Finset.mem_image.mpr
    refine ⟨readSeed P slots v a, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨registerCoord a, Finset.mem_univ _, rfl⟩
  · intro h
    obtain ⟨s, hs, hsn⟩ := Finset.mem_image.mp h
    obtain ⟨a, _, has⟩ := Finset.mem_image.mp hs
    apply List.mem_ofFn.mpr
    cases a with
    | inl u =>
      cases u
      exact ⟨0, (congrArg (seedCode vertices factors Δ) has).trans hsn⟩
    | inr i =>
      refine ⟨i.succ, ?_⟩
      simpa [readSeed, registerCoord] using
        (congrArg (seedCode vertices factors Δ) has).trans hsn

def pairPlan (vertices : List V) (factors : List E) (pair : V × V) : List ℕ :=
  vertexPlan P slots vertices factors pair.1 ++ vertexPlan P slots vertices factors pair.2

@[simp] theorem pairPlan_length (vertices : List V) (factors : List E) (pair : V × V) :
    (pairPlan P slots vertices factors pair).length = 2 * (Δ + 1) := by
  simp [pairPlan]
  omega

theorem mem_pairPlan_iff (vertices : List V) (factors : List E) (pair : V × V) (n : ℕ) :
    n ∈ pairPlan P slots vertices factors pair ↔
      n ∈ LocalExpectation.numberedPairSupport P slots (seedIndices vertices factors Δ) pair := by
  simp only [pairPlan, List.mem_append, mem_vertexPlan_iff,
    LocalExpectation.numberedPairSupport, pairSupport, SubexponentialSAT.TypeDistribution.pairSupport,
    Finset.image_union, Finset.mem_union ]
  rfl

/-- Test only numeric membership in the two explicit vertex plans. -/
def remainingPlan (vertices : List V) (factors : List E) (pair : V × V)
    (fixedCount remainingCount : ℕ) : List ℕ :=
  (List.range' fixedCount remainingCount).filter
    (fun n => decide (n ∈ pairPlan P slots vertices factors pair))

theorem remainingPlan_eq_active (vertices : List V) (factors : List E) (pair : V × V)
    (fixedCount remainingCount : ℕ) :
    remainingPlan P slots vertices factors pair fixedCount remainingCount =
      SubexponentialSAT.LocalExpectation.active
        (LocalExpectation.numberedPairSupport P slots (seedIndices vertices factors Δ) pair)
        (List.range' fixedCount remainingCount) := by
  unfold remainingPlan SubexponentialSAT.LocalExpectation.active
  congr 1
  funext n
  simp only [mem_pairPlan_iff]

theorem remainingPlan_nodup (vertices : List V) (factors : List E) (pair : V × V)
    (fixedCount remainingCount : ℕ) :
    (remainingPlan P slots vertices factors pair fixedCount remainingCount).Nodup := by
  have h : (List.range' fixedCount remainingCount).Nodup := List.nodup_range'
  exact h.filter _

theorem remainingPlan_length_le (vertices : List V) (factors : List E) (pair : V × V)
    (fixedCount remainingCount : ℕ) :
    (remainingPlan P slots vertices factors pair fixedCount remainingCount).length ≤ 2 * (Δ + 1) := by
  rw [remainingPlan_eq_active]
  exact (SubexponentialSAT.LocalExpectation.active_length_le _ _ List.nodup_range').trans
    (LocalExpectation.numberedPairSupport_card_le P slots (seedIndices vertices factors Δ) pair)

def seedWords (vertices : List V) (factors : List E)
    (ω : Assignment V E r Q Δ) : List (Word r Q) :=
  (seedIndices vertices factors Δ).map ω

def seedRows (vertices : List V) (factors : List E)
    (ω : Assignment V E r Q Δ) : List (List Bool) :=
  (seedWords vertices factors ω).map encodeWord

theorem gather_seedWords (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (ω : Assignment V E r Q Δ) (v : V) :
    gather default (seedWords vertices factors ω) (vertexPlan P slots vertices factors v) =
      List.ofFn (fun a : Fin (Δ + 1) =>
        CollisionProgram.registerWord (assignmentType P slots ω v) a) := by
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  simp only [gather, vertexPlan, List.map_ofFn]
  congr 1
  funext a
  rw [registerWord_assignmentType]
  simp only [seedWords, seedCode, SubexponentialSAT.LocalExpectation.indexCode,
    List.getD_eq_getElem?_getD, List.getElem?_map, Function.comp_apply,
    List.getElem?_idxOf (mem_seedIndices vertices factors Δ hv he _)]
  rfl

theorem gather_seedRows (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (ω : Assignment V E r Q Δ) (v : V) :
    (gather [] (seedRows vertices factors ω)
      (vertexPlan P slots vertices factors v)).flatten =
      CollisionProgram.encodeType (assignmentType P slots ω v) := by
  let _ : BEq (SeedIndex V E Δ) := instBEqOfDecidableEq
  rw [encodeType_eq_words]
  congr 1
  simp only [gather, vertexPlan, List.map_ofFn]
  congr 1
  funext a
  rw [registerWord_assignmentType]
  simp only [seedRows, seedWords, seedCode, SubexponentialSAT.LocalExpectation.indexCode,
    List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, Function.comp_apply,
    List.getElem?_idxOf (mem_seedIndices vertices factors Δ hv he _)]
  rfl

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
theorem seedRows_width (vertices : List V) (factors : List E)
    (ω : Assignment V E r Q Δ) (row : List Bool) (hrow : row ∈ seedRows vertices factors ω) :
    row.length = wordWidth r Q := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hrow
  exact encodeWord_length w

end VertexPlans

section PartialAssignments

variable {W : Type*}

/-- A free seed reads its candidate-tuple position after the current array;
every other seed keeps its original current-array position. -/
def selectPosition (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) : ℕ :=
  if n ∈ remaining then currentSize + remaining.idxOf n else n

def completionPlan (currentSize : ℕ) (remaining plan : List ℕ) : List ℕ :=
  plan.map (selectPosition currentSize remaining)

/-- First-match lookup table for the selector, built by one finite recursion. -/
def selectionTable (currentSize : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | n :: remaining => (n, currentSize) :: selectionTable (currentSize + 1) remaining

@[simp] theorem selectionTable_length (currentSize : ℕ) (remaining : List ℕ) :
    (selectionTable currentSize remaining).length = remaining.length := by
  induction remaining generalizing currentSize with
  | nil => rfl
  | cons n remaining ih => simp [selectionTable, ih]

theorem selectionTable_lookup (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) :
    (selectionTable currentSize remaining).lookup n =
      if n ∈ remaining then some (currentSize + remaining.idxOf n) else none := by
  induction remaining generalizing currentSize with
  | nil => simp [selectionTable]
  | cons a remaining ih =>
    by_cases hna : n = a
    · subst n
      simp [selectionTable ]
    · simp [selectionTable, List.lookup_cons, hna, Ne.symm hna, beq_false_of_ne hna, ih, Nat.add_comm, Nat.add_left_comm]

theorem selectionTable_lookup_default (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) :
    ((selectionTable currentSize remaining).lookup n).getD n =
      selectPosition currentSize remaining n := by
  rw [selectionTable_lookup]
  unfold selectPosition
  split_ifs <;> rfl

theorem selectionTable_value_bounds (currentSize : ℕ) (remaining : List ℕ)
    (n v : ℕ) (h : (n, v) ∈ selectionTable currentSize remaining) :
    currentSize ≤ v ∧ v < currentSize + remaining.length := by
  induction remaining generalizing currentSize with
  | nil => simp [selectionTable] at h
  | cons a remaining ih =>
    simp only [selectionTable, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩ | h
    · simp
    · have ht := ih (currentSize + 1) h
      simp only [List.length_cons]
      omega

def completedAt (default : W) (current : List W) (remaining : List ℕ)
    (candidate : List W) (n : ℕ) : W :=
  if n ∈ remaining then candidate.getD (remaining.idxOf n) default
  else current.getD n default

theorem selected_getD (default : W) (current : List W) (remaining : List ℕ)
    (candidate : List W) (n : ℕ) (hn : n < current.length) :
    (current ++ candidate).getD (selectPosition current.length remaining n) default =
      completedAt default current remaining candidate n := by
  by_cases hm : n ∈ remaining
  · simp only [selectPosition, completedAt, ite_eq_left hm]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  · simp only [selectPosition, completedAt, ite_eq_right hm]
    exact List.getD_append _ _ _ _ hn

theorem selected_valid (currentSize candidateSize : ℕ) (remaining : List ℕ)
    (hlen : remaining.length ≤ candidateSize) (n : ℕ) (hn : n < currentSize) :
    selectPosition currentSize remaining n < currentSize + candidateSize := by
  by_cases hm : n ∈ remaining
  · have hi := List.idxOf_lt_length_iff.mpr hm
    simp only [selectPosition, ite_eq_left hm]
    omega
  · simp only [selectPosition, ite_eq_right hm]
    omega

@[simp] theorem completionPlan_length (currentSize : ℕ) (remaining plan : List ℕ) :
    (completionPlan currentSize remaining plan).length = plan.length := by
  simp [completionPlan]

theorem completionPlan_valid (currentSize candidateSize : ℕ) (remaining plan : List ℕ)
    (hlen : remaining.length ≤ candidateSize) (hp : ∀ n ∈ plan, n < currentSize)
    (n : ℕ) (hn : n ∈ completionPlan currentSize remaining plan) :
    n < currentSize + candidateSize := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hn
  exact selected_valid currentSize candidateSize remaining hlen j (hp j hj)

/-- The optional-coordinate update semantics used by the padded leaf tree,
driven by one explicit list of candidate words. -/
def applyChoices (current : ℕ → W) : List (Option ℕ) → List W → ℕ → W
  | [], _ => current
  | _ :: _, [] => current
  | i :: remaining, w :: candidate =>
      applyChoices (PaddedCompletion.assignOptional current i w) remaining candidate

theorem applyChoices_none (current : ℕ → W) (padding : ℕ) (candidate : List W) :
    applyChoices current (List.replicate padding none) candidate = current := by
  induction padding generalizing current candidate with
  | zero => rfl
  | succ padding ih =>
    cases candidate with
    | nil => rfl
    | cons w candidate =>
      simpa [List.replicate_succ, applyChoices, PaddedCompletion.assignOptional] using
        (ih current candidate)

theorem applyChoices_padding (current : ℕ → W) (remaining : List ℕ)
    (padding : ℕ) (candidate : List W) :
    applyChoices current (remaining.map some ++ List.replicate padding none) candidate =
      applyChoices current (remaining.map some) candidate := by
  induction remaining generalizing current candidate with
  | nil => simpa [applyChoices] using applyChoices_none current padding candidate
  | cons i remaining ih =>
    cases candidate with
    | nil => rfl
    | cons w candidate =>
      simpa only [List.map_cons, List.cons_append, applyChoices] using
        ih (PaddedCompletion.assignOptional current (some i) w) candidate

theorem applyChoices_real (default : W) (current : ℕ → W)
    (remaining : List ℕ) (candidate : List W) (hn : remaining.Nodup)
    (hlen : remaining.length ≤ candidate.length) (n : ℕ) :
    applyChoices current (remaining.map some) candidate n =
      if n ∈ remaining then candidate.getD (remaining.idxOf n) default else current n := by
  induction remaining generalizing current candidate with
  | nil => simp [applyChoices]
  | cons i remaining ih =>
    cases candidate with
    | nil => simp at hlen
    | cons w candidate =>
      have ht : remaining.length ≤ candidate.length := by simpa using hlen
      simp only [List.map_cons, applyChoices]
      rw [ih _ _ hn.of_cons ht]
      by_cases hni : n = i
      · subst n
        have hi : i ∉ remaining := (List.nodup_cons.mp hn).1
        simp [hi, PaddedCompletion.assignOptional]
      · simp [hni, Ne.symm hni, PaddedCompletion.assignOptional, Function.update_of_ne]

theorem applyChoices_padded (default : W) (current : List W)
    (remaining : List ℕ) (candidate : List W) (S : ℕ)
    (hn : remaining.Nodup) (hlen : remaining.length ≤ candidate.length) (n : ℕ) :
    applyChoices (fun j => current.getD j default)
      (PaddedCompletion.paddedIndices remaining S) candidate n =
        completedAt default current remaining candidate n := by
  unfold PaddedCompletion.paddedIndices
  rw [applyChoices_padding, applyChoices_real default _ _ _ hn hlen]
  rfl

/-- Each actual leaf is obtained by one explicit tuple in the same recursive
order as the padded completion tree. -/
theorem leaves_eq_tuples (alphabet : List W) (f : (ℕ → W) → Bool)
    (remaining : List (Option ℕ)) (current : ℕ → W) :
    PaddedCompletion.leaves alphabet f remaining current =
      (CoefficientSearch.tuples alphabet remaining.length).map
        (fun candidate => f (applyChoices current remaining (List.ofFn candidate))) := by
  induction remaining generalizing current with
  | nil => simp [PaddedCompletion.leaves, CoefficientSearch.tuples, applyChoices]
  | cons i remaining ih =>
    simp only [PaddedCompletion.leaves, List.length_cons, CoefficientSearch.tuples,
      List.map_flatMap]
    apply congrArg (fun g => alphabet.flatMap g)
    funext w
    rw [ih]
    simp only [List.map_map]
    congr 1
    funext candidate
    simp [ List.ofFn_succ, applyChoices]

end PartialAssignments

section PartialVertexPlans

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} (slots : SlotMap P Δ)

def completedAssignment (vertices : List V) (factors : List E)
    (default : Word r Q) (current : List (Word r Q)) (remaining : List ℕ)
    (candidate : List (Word r Q)) : Assignment V E r Q Δ :=
  fun s => completedAt default current remaining candidate (seedCode vertices factors Δ s)

/-- Bit records for the current words followed by the candidate tuple. -/
def partialEncoding (vertices : List V) (factors : List E)
    (current : List (Word r Q)) (remaining : List ℕ) (candidate : List (Word r Q))
    (v : V) : List Bool :=
  (gather [] ((current ++ candidate).map encodeWord)
    (completionPlan current.length remaining (vertexPlan P slots vertices factors v))).flatten

theorem partialEncoding_eq (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (current : List (Word r Q)) (remaining : List ℕ)
    (candidate : List (Word r Q))
    (hc : (seedIndices vertices factors Δ).length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (v : V) :
    partialEncoding P slots vertices factors current remaining candidate v =
      CollisionProgram.encodeType
        (assignmentType P slots (completedAssignment vertices factors default current remaining candidate) v) := by
  rw [encodeType_eq_words]
  unfold partialEncoding gather completionPlan vertexPlan
  simp only [ List.map_ofFn, Function.comp_def]
  congr 2
  funext a
  have hseed : seedCode vertices factors Δ (readSeed P slots v a) <
      (seedIndices vertices factors Δ).length := by
    simpa only [seedIndices_length] using
      seedCode_lt vertices factors Δ hv he (readSeed P slots v a)
  have hn := hseed.trans_le hc
  have hs := selected_valid current.length candidate.length remaining hr _ hn
  rw [getD_map_of_lt encodeWord _ default [] _ (by simpa using hs),
    selected_getD default current remaining candidate _ hn,
    registerWord_assignmentType]
  rfl

/-- A finite, explicit current array from the search's reverse fixed list. -/
def currentArray (default : Word r Q) (seedCount : ℕ) (fixed : List (Word r Q)) :
    List (Word r Q) :=
  (List.range seedCount).map (SubexponentialSAT.LocalExpectation.decode default fixed)

@[simp] theorem currentArray_length (default : Word r Q) (seedCount : ℕ)
    (fixed : List (Word r Q)) : (currentArray default seedCount fixed).length = seedCount := by
  simp [currentArray]

theorem currentArray_getD (default : Word r Q) (seedCount : ℕ)
    (fixed : List (Word r Q)) (n : ℕ) (hn : n < seedCount) :
    (currentArray default seedCount fixed).getD n default =
      SubexponentialSAT.LocalExpectation.decode default fixed n := by
  simp [currentArray, List.getD_eq_getElem?_getD, List.getElem?_range hn]

def leafAssignment (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remaining : List ℕ)
    (candidate : List (Word r Q)) (S : ℕ) : Assignment V E r Q Δ :=
  fun s => applyChoices (SubexponentialSAT.LocalExpectation.decode default fixed)
    (PaddedCompletion.paddedIndices remaining S) candidate (seedCode vertices factors Δ s)

omit [Fintype E] in
/-- The preparation uses the actual search state and tuple, and reconstructs
the actual optional-update leaf assignment at every seed coordinate. -/
theorem completedAssignment_eq_leaf (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remaining : List ℕ)
    (candidate : List (Word r Q)) (S : ℕ)
    (hn : remaining.Nodup) (hr : remaining.length ≤ candidate.length) :
    completedAssignment (Δ := Δ) vertices factors default
        (currentArray default (seedIndices vertices factors Δ).length fixed) remaining candidate =
      leafAssignment (Δ := Δ) vertices factors default fixed remaining candidate S := by
  funext s
  unfold completedAssignment leafAssignment PaddedCompletion.paddedIndices
  rw [applyChoices_padding, applyChoices_real default _ _ _ hn hr]
  unfold completedAt
  split_ifs
  · rfl
  · exact currentArray_getD default _ fixed _
      (by simpa only [seedIndices_length] using seedCode_lt vertices factors Δ hv he s)

theorem partialEncoding_fixed_eq_leaf (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remaining : List ℕ)
    (candidate : List (Word r Q)) (S : ℕ)
    (hn : remaining.Nodup) (hr : remaining.length ≤ candidate.length) (v : V) :
    partialEncoding P slots vertices factors
        (currentArray default (seedIndices vertices factors Δ).length fixed) remaining candidate v =
      CollisionProgram.encodeType
        (assignmentType P slots (leafAssignment vertices factors default fixed remaining candidate S) v) := by
  rw [partialEncoding_eq P slots vertices factors hv he default _ _ _
    (by simp) hr v, completedAssignment_eq_leaf vertices factors hv he default fixed remaining candidate S hn hr]

end PartialVertexPlans

section CollisionLeaves

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r] (slots : SlotMap P Δ)

/-- This local test compares two explicit bit lists. -/
def plannedCollision (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remaining : List ℕ)
    (candidate : List (Word r Q)) (pair : V × V) : Bool :=
  let current := currentArray default (seedIndices vertices factors Δ).length fixed
  partialEncoding P slots vertices factors current remaining candidate pair.1 ==
    partialEncoding P slots vertices factors current remaining candidate pair.2

omit [Fintype V] [NeZero r] in
theorem plannedCollision_eq_leaf (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remaining : List ℕ)
    (candidate : List (Word r Q)) (S : ℕ) (hn : remaining.Nodup)
    (hr : remaining.length ≤ candidate.length) (pair : V × V) :
    plannedCollision P slots vertices factors default fixed remaining candidate pair =
      decide (NaturalAssignment.numberedNaturalPairTerm P slots (seedIndices vertices factors Δ) pair
        (applyChoices (SubexponentialSAT.LocalExpectation.decode default fixed)
          (PaddedCompletion.paddedIndices remaining S) candidate) = 1) := by
  dsimp only [plannedCollision]
  rw [partialEncoding_fixed_eq_leaf P slots vertices factors hv he default fixed remaining candidate S hn hr,
    partialEncoding_fixed_eq_leaf P slots vertices factors hv he default fixed remaining candidate S hn hr]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, CollisionProgram.encodeType_eq_iff]
  change _ ↔ (if _ then (1 : ℕ) else 0) = 1
  split_ifs with h
  · exact iff_of_true h rfl
  · exact iff_of_false h (by decide)

/-- A concrete pair leaf stream, generated from tuple words and list reads. -/
def plannedPairLeaves (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) : List Bool :=
  let remaining := remainingPlan P slots vertices factors pair fixed.length remainingCount
  let padded := PaddedCompletion.paddedIndices remaining (2 * (Δ + 1))
  (CoefficientSearch.tuples alphabet padded.length).map (fun candidate =>
    plannedCollision P slots vertices factors default fixed remaining (List.ofFn candidate) pair)

omit [Fintype V] [NeZero r] in
theorem plannedPairLeaves_eq (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) :
    plannedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair =
      PaddedCompletion.paddedLeaves alphabet
        (fun ξ => decide (NaturalAssignment.numberedNaturalPairTerm P slots
          (seedIndices vertices factors Δ) pair ξ = 1))
        (SubexponentialSAT.LocalExpectation.active
          (LocalExpectation.numberedPairSupport P slots (seedIndices vertices factors Δ) pair)
          (List.range' fixed.length remainingCount))
        (2 * (Δ + 1)) (SubexponentialSAT.LocalExpectation.decode default fixed) := by
  rw [← remainingPlan_eq_active]
  dsimp only [plannedPairLeaves, PaddedCompletion.paddedLeaves]
  rw [leaves_eq_tuples]
  congr 1
  funext candidate
  apply plannedCollision_eq_leaf P slots vertices factors hv he default fixed _ _ _
    (remainingPlan_nodup P slots vertices factors pair fixed.length remainingCount)
  rw [List.length_ofFn, PaddedCompletion.paddedIndices_length _ _
    (remainingPlan_length_le P slots vertices factors pair fixed.length remainingCount)]
  exact remainingPlan_length_le P slots vertices factors pair fixed.length remainingCount

omit [Fintype V] [NeZero r] in
theorem plannedPairLeaves_length (alphabet : List (Word r Q))
    (vertices : List V) (factors : List E) (default : Word r Q)
    (fixed : List (Word r Q)) (remainingCount : ℕ) (pair : V × V) :
    (plannedPairLeaves P slots alphabet vertices factors default fixed remainingCount pair).length =
      alphabet.length ^ (2 * (Δ + 1)) := by
  simp only [plannedPairLeaves, List.length_map, CoefficientSearch.tuples_length]
  rw [PaddedCompletion.paddedIndices_length _ _
    (remainingPlan_length_le P slots vertices factors pair fixed.length remainingCount)]

/-- Assemble all ordered-pair streams using the same explicit vertex list. -/
def plannedNumeratorLeaves (alphabet : List (Word r Q)) (vertices : List V) (factors : List E)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) : List Bool :=
  (vertices.product vertices).flatMap
    (plannedPairLeaves P slots alphabet vertices factors default fixed remainingCount)

omit [Fintype V] [NeZero r] in
theorem plannedNumeratorLeaves_eq (alphabet : List (Word r Q))
    (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) :
    plannedNumeratorLeaves P slots alphabet vertices factors default fixed remainingCount =
      NaturalAssignment.sequentialNumeratorLeaves P slots alphabet vertices
        (seedIndices vertices factors Δ) default remainingCount fixed := by
  unfold plannedNumeratorLeaves NaturalAssignment.sequentialNumeratorLeaves
    PaddedCompletion.numeratorLeaves
  congr 1
  funext pair
  exact plannedPairLeaves_eq P slots alphabet vertices factors hv he default fixed remainingCount pair

omit [Fintype V] [NeZero r] in
theorem plannedNumeratorLeaves_trueCount (alphabet : List (Word r Q))
    (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed : List (Word r Q)) (remainingCount : ℕ) :
    (PaddedCompletion.successful
      (plannedNumeratorLeaves P slots alphabet vertices factors default fixed remainingCount)).length =
      NaturalAssignment.sequentialNumerator P slots alphabet vertices
        (seedIndices vertices factors Δ) default remainingCount fixed := by
  rw [plannedNumeratorLeaves_eq P slots alphabet vertices factors hv he]
  exact NaturalAssignment.sequentialNumeratorLeaves_trueCount P slots alphabet vertices _ default _ fixed

end CollisionLeaves

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
