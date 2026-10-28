import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.MulticolorTypes
import OAI.Algorithms.SubexponentialSAT.TypeDistribution

namespace OAI.Algorithms

/-!
# Multicolor type assignment, explicit counts, and variance

This is Section 3.4 of the subexponential manuscript. Every parameter, including
the number r of colors, remains explicit. The probability space consists of
actual independent words at factor, head, and padding indices. Uniformity and
independence are proved from injective/disjoint coordinate reads.

The local completion bound is the square of the universal type cardinality.
No construction cost is hidden in a constant depending on r, Q, or Δ.
-/

namespace SubexponentialSAT.SubexpTypeVariance

open scoped BigOperators
open SubexponentialSAT.Factor SubexponentialSAT.SlotAssignment SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes

abbrev SeedIndex (V E : Type*) (Δ : ℕ) := SubexponentialSAT.TypeDistribution.SeedIndex V E Δ
abbrev Assignment (V E : Type*) (r Q Δ : ℕ) := SeedIndex V E Δ → Word r Q
abbrev LocalCoord (Δ : ℕ) := SubexponentialSAT.TypeDistribution.LocalCoord Δ

/-- A head word and one word for each slot are exactly a multicolor type. -/
def wordTypeEquiv (r Q Δ : ℕ) : (LocalCoord Δ → Word r Q) ≃ UniversalType r Q Δ where
  toFun f := ⟨f (.inl ()), fun i => f (.inr i)⟩
  invFun u := Sum.elim (fun _ => u.head) u.slot
  left_inv f := by
    funext a
    rcases a with ⟨⟩ | i <;> rfl
  right_inv u := by cases u; rfl

section Assignments

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable (P : Pattern V E) {r Q Δ : ℕ} (slots : SlotMap P Δ)

/-- The multicolor type read by a coordinate from the independent word assignment. -/
def assignmentType (ω : Assignment V E r Q Δ) (v : V) : UniversalType r Q Δ :=
  wordTypeEquiv r Q Δ (fun a => ω (SubexponentialSAT.TypeDistribution.reads P slots v a))

omit [DecidableEq E] in
theorem assignmentType_eq_typeFromWords (ω : Assignment V E r Q Δ) (v : V) :
    assignmentType P slots ω v =
      SubexponentialSAT.MulticolorTypes.typeFromWords P slots
        (fun e => ω (.inl e)) (fun v => ω (.inr (.inl v)))
        (fun v i => ω (.inr (.inr (v, i)))) v := by
  apply UniversalType.ext
  · rfl
  · funext i
    by_cases h : ∃ e, slots v e = i
    · obtain ⟨e, rfl⟩ := h
      change ω (SubexponentialSAT.TypeDistribution.reads P slots v (.inr (slots v e))) = _
      rw [SubexponentialSAT.TypeDistribution.reads_used, SubexponentialSAT.MulticolorTypes.typeFromWords_incidence]
    · change ω (SubexponentialSAT.TypeDistribution.reads P slots v (.inr i)) = _
      rw [SubexponentialSAT.TypeDistribution.reads_unused P slots v ⟨i, h⟩,
        SubexponentialSAT.MulticolorTypes.typeFromWords_unused P slots _ _ _ v i h]

omit [DecidableEq E] in
@[simp] theorem assignmentType_incidence (ω : Assignment V E r Q Δ)
    (v : V) (e : Incident P v) :
    (assignmentType P slots ω v).slot (slots v e) = ω (.inl e.val) := by
  rw [assignmentType_eq_typeFromWords, SubexponentialSAT.MulticolorTypes.typeFromWords_incidence]

abbrev readSupport (v : V) : Finset (SeedIndex V E Δ) :=
  SubexponentialSAT.TypeDistribution.readSupport P slots v

abbrev pairSupport (v w : V) : Finset (SeedIndex V E Δ) :=
  SubexponentialSAT.TypeDistribution.pairSupport P slots v w

theorem readSupport_card (v : V) : (readSupport P slots v).card = Δ + 1 :=
  SubexponentialSAT.TypeDistribution.readSupport_card P slots v

theorem pairSupport_card_le (v w : V) :
    (pairSupport P slots v w).card ≤ 2 * (Δ + 1) :=
  SubexponentialSAT.TypeDistribution.pairSupport_card_le P slots v w

theorem assignmentType_congr (ω ω' : Assignment V E r Q Δ) (v : V)
    (h : ∀ i ∈ readSupport P slots v, ω i = ω' i) :
    assignmentType P slots ω v = assignmentType P slots ω' v := by
  unfold assignmentType
  congr 1
  funext a
  exact h _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

def pairCollision (ω : Assignment V E r Q Δ) (v w : V) : ℚ :=
  if assignmentType P slots ω v = assignmentType P slots ω w then 1 else 0

theorem pairCollision_congr (ω ω' : Assignment V E r Q Δ) (v w : V)
    (h : ∀ i ∈ pairSupport P slots v w, ω i = ω' i) :
    pairCollision P slots ω v w = pairCollision P slots ω' v w := by
  have hv := assignmentType_congr P slots ω ω' v
    (fun i hi => h i (Finset.mem_union_left _ hi))
  have hw := assignmentType_congr P slots ω ω' w
    (fun i hi => h i (Finset.mem_union_right _ hi))
  simp only [pairCollision, hv, hw]

variable [Fintype V] [NeZero r]

/-- Exact uniform marginal law for every coordinate type, for every r > 0. -/
theorem mean_assignmentType (v : V) (F : UniversalType r Q Δ → ℚ) :
    mean uniformWeight
      (fun ω : Assignment V E r Q Δ => F (assignmentType P slots ω v)) =
        mean uniformWeight F := by
  calc
    _ = mean uniformWeight
        (fun ξ : LocalCoord Δ → Word r Q => F (wordTypeEquiv r Q Δ ξ)) :=
      SubexponentialSAT.TypeDistribution.mean_restrict (SubexponentialSAT.TypeDistribution.reads P slots v) _
    _ = _ := SubexponentialSAT.TypeDistribution.mean_equiv (wordTypeEquiv r Q Δ) F

/-- Full pair-moment independence for coordinates that share no factor. -/
theorem mean_assignmentType_mul {v w : V} (hvw : v ≠ w)
    (hshare : ∀ e, v ∈ P.scope e → w ∉ P.scope e)
    (F G : UniversalType r Q Δ → ℚ) :
    mean uniformWeight (fun ω : Assignment V E r Q Δ =>
      F (assignmentType P slots ω v) * G (assignmentType P slots ω w)) =
        mean uniformWeight F * mean uniformWeight G := by
  calc
    _ = mean uniformWeight
          (fun ξ : LocalCoord Δ → Word r Q => F (wordTypeEquiv r Q Δ ξ)) *
        mean uniformWeight
          (fun ξ : LocalCoord Δ → Word r Q => G (wordTypeEquiv r Q Δ ξ)) :=
      SubexponentialSAT.TypeDistribution.mean_restrict_mul
        (SubexponentialSAT.TypeDistribution.reads P slots v) (SubexponentialSAT.TypeDistribution.reads P slots w)
        (SubexponentialSAT.TypeDistribution.reads_ne P slots hvw hshare) _ _
    _ = _ := by rw [SubexponentialSAT.TypeDistribution.mean_equiv, SubexponentialSAT.TypeDistribution.mean_equiv]

theorem assignmentType_marginal (u : UniversalType r Q Δ) (v : V) :
    mean uniformWeight (fun ω : Assignment V E r Q Δ =>
      typeIndicator (assignmentType P slots) u ω v) =
        1 / (Fintype.card (UniversalType r Q Δ) : ℚ) :=
  (mean_assignmentType P slots v (fun a => if a = u then (1 : ℚ) else 0)).trans
    (SubexponentialSAT.TypeDistribution.mean_indicator u)

theorem assignmentType_independent (u : UniversalType r Q Δ) {v w : V} (hvw : v ≠ w)
    (hshare : ∀ e, v ∈ P.scope e → w ∉ P.scope e) :
    mean uniformWeight (fun ω : Assignment V E r Q Δ =>
      typeIndicator (assignmentType P slots) u ω v *
        typeIndicator (assignmentType P slots) u ω w) =
      (1 / (Fintype.card (UniversalType r Q Δ) : ℚ)) *
        (1 / (Fintype.card (UniversalType r Q Δ) : ℚ)) := by
  calc
    _ = mean uniformWeight (fun a => if a = u then (1 : ℚ) else 0) *
        mean uniformWeight (fun a => if a = u then (1 : ℚ) else 0) :=
      mean_assignmentType_mul P slots hvw hshare _ _
    _ = _ := by rw [SubexponentialSAT.TypeDistribution.mean_indicator]

/-- The count has its claimed exact expected value D/N, with N displayed. -/
theorem mean_typeCount_explicit (u : UniversalType r Q Δ) :
    mean uniformWeight (fun ω : Assignment V E r Q Δ =>
      (typeCount (assignmentType P slots) u ω : ℚ)) =
        (Fintype.card V : ℚ) / ((r ^ (Q * (Δ + 1)) : ℕ) : ℚ) := by
  simpa only [card_universalType] using
    mean_typeCount uniformWeight (assignmentType P slots) u
      (fun v => assignmentType_marginal P slots u v)

omit [DecidableEq E] in
/-- The collision identity makes every conditional expectation a sum of
functions of at most 2(Δ+1) word variables, plus a fixed constant. -/
theorem assignment_deviation_eq_collisions (ω : Assignment V E r Q Δ) :
    (∑ u : UniversalType r Q Δ,
      ((typeCount (assignmentType P slots) u ω : ℚ) -
        (Fintype.card V : ℚ) / (Fintype.card (UniversalType r Q Δ) : ℚ)) ^ 2) =
      (∑ v : V, ∑ w : V, pairCollision P slots ω v w) -
        (Fintype.card V : ℚ) ^ 2 / (Fintype.card (UniversalType r Q Δ) : ℚ) := by
  let _ : Nonempty (UniversalType r Q Δ) :=
    ⟨⟨fun _ => 0, fun _ _ => 0⟩⟩
  exact SubexponentialSAT.TypeDistribution.squared_deviation_eq_collisions (assignmentType P slots ω)

/-- Expected discrepancy for the actual independent-word distribution. -/
theorem mean_squared_deviation_le {k : ℕ} (hP : P.Bounded k Δ) :
    mean uniformWeight (fun ω : Assignment V E r Q Δ =>
      ∑ u : UniversalType r Q Δ,
        ((typeCount (assignmentType P slots) u ω : ℚ) -
          (Fintype.card V : ℚ) / (Fintype.card (UniversalType r Q Δ) : ℚ)) ^ 2) ≤
      (Fintype.card (UniversalType r Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  apply sum_typeCount_variances_le uniformWeight uniformWeight_nonneg uniformWeight_sum
    (assignmentType P slots) (assignmentType_marginal P slots)
    (SubexponentialSAT.Incidence.dependencyNeighbors P.scope) (Δ * k)
  · intro v
    exact (SubexponentialSAT.Incidence.bounded_card_dependencyNeighbors_le P v k Δ hP).trans
      (Nat.mul_le_mul_left Δ (Nat.sub_le k 1))
  · intro u v w hvw hn
    apply assignmentType_independent P slots u hvw
    intro e hv hw
    apply hn
    exact (SubexponentialSAT.Incidence.mem_dependencyNeighbors P.scope v w).mpr
      ⟨Ne.symm hvw, e, hv, hw⟩

/-- The same estimate with every growing parameter visible. -/
theorem mean_squared_deviation_le_explicit {k : ℕ} (hP : P.Bounded k Δ) :
    mean uniformWeight (fun ω : Assignment V E r Q Δ =>
      ∑ u : UniversalType r Q Δ,
        ((typeCount (assignmentType P slots) u ω : ℚ) -
          (Fintype.card V : ℚ) / ((r ^ (Q * (Δ + 1)) : ℕ) : ℚ)) ^ 2) ≤
      ((r ^ (Q * (Δ + 1)) : ℕ) : ℚ) *
        (1 + ((Δ * k : ℕ) : ℚ)) * (Fintype.card V : ℚ) := by
  simpa only [card_universalType] using mean_squared_deviation_le P slots hP

theorem exists_assignment_deviation_le {k : ℕ} (hP : P.Bounded k Δ) :
    ∃ ω : Assignment V E r Q Δ,
      (∑ u : UniversalType r Q Δ,
        ((typeCount (assignmentType P slots) u ω : ℚ) -
          (Fintype.card V : ℚ) / (Fintype.card (UniversalType r Q Δ) : ℚ)) ^ 2) ≤
        (Fintype.card (UniversalType r Q Δ) : ℚ) *
          (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  apply SubexponentialSAT.ConditionalExpectation.exists_le_of_uniform_mean_le
  rw [← mean_uniformWeight]
  exact mean_squared_deviation_le P slots hP

/-- Consistent factor colors and a concrete type assignment with the discrepancy
bound needed for full-block packing. -/
theorem exists_consistent_types_deviation_le {k : ℕ} (hP : P.Bounded k Δ) :
    ∃ (sigma : E → Word r Q) (τ : V → UniversalType r Q Δ),
      (∀ (v : V) (e : Incident P v), (τ v).slot (slots v e) = sigma e.val) ∧
      (∑ u : UniversalType r Q Δ,
        (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
          (Fintype.card V : ℚ) / (Fintype.card (UniversalType r Q Δ) : ℚ)) ^ 2) ≤
        (Fintype.card (UniversalType r Q Δ) : ℚ) *
          (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  obtain ⟨ω, hω⟩ := exists_assignment_deviation_le (r := r) (Q := Q) P slots hP
  refine ⟨fun e => ω (.inl e), assignmentType P slots ω, ?_, hω⟩
  intro v e
  exact assignmentType_incidence P slots ω v e

end Assignments

section ExplicitEnumerationCounts

variable {r Q Δ : ℕ} [NeZero r]

theorem word_choices_le_type_choices :
    r ^ Q ≤ r ^ (Q * (Δ + 1)) := by
  apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne r))
  calc
    Q = Q * 1 := by omega
    _ ≤ Q * (Δ + 1) := Nat.mul_le_mul_left Q (by omega)

/-- Completing at most two local read sets requires at most N² assignments. -/
theorem completion_count_le_type_choices_sq {s : ℕ} (hs : s ≤ 2 * (Δ + 1)) :
    (r ^ Q) ^ s ≤ (r ^ (Q * (Δ + 1))) ^ 2 := by
  calc
    (r ^ Q) ^ s ≤ (r ^ Q) ^ (2 * (Δ + 1)) :=
      Nat.pow_le_pow_right (pow_pos (Nat.pos_of_ne_zero (NeZero.ne r)) Q) hs
    _ = (r ^ (Q * (Δ + 1))) ^ 2 := by
      simp only [← pow_mul]
      congr 1
      ring

theorem pair_completion_count_le {V E : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype E]
    (P : Pattern V E) (slots : SlotMap P Δ) (v w : V) :
    (Fintype.card (Word r Q)) ^ (pairSupport P slots v w).card ≤
      (Fintype.card (UniversalType r Q Δ)) ^ 2 := by
  simpa only [card_word, card_universalType] using
    completion_count_le_type_choices_sq (r := r) (Q := Q) (pairSupport_card_le P slots v w)

theorem card_seedIndex {V E : Type*} [Fintype V] [Fintype E] :
    Fintype.card (SeedIndex V E Δ) =
      Fintype.card E + (Fintype.card V + Fintype.card V * Δ) := by
  simp [SeedIndex, SubexponentialSAT.TypeDistribution.SeedIndex]

theorem card_seedIndex_le {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (P : Pattern V E) {k : ℕ} (hP : P.Bounded k Δ) :
    Fintype.card (SeedIndex V E Δ) ≤ (2 * Δ + 1) * Fintype.card V := by
  calc
    _ = Fintype.card E + (Fintype.card V + Fintype.card V * Δ) := card_seedIndex
    _ ≤ Δ * Fintype.card V + (Fintype.card V + Fintype.card V * Δ) :=
      Nat.add_le_add_right (SubexponentialSAT.Incidence.bounded_card_factors_le P k Δ hP) _
    _ = _ := by ring

end ExplicitEnumerationCounts

end SubexponentialSAT.SubexpTypeVariance

end OAI.Algorithms
