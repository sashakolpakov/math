import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicBoundaryReindex

/-! # Logarithmic Etale Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicEtaleMap.Construction

noncomputable section

section

/-! Logarithmic bounds under actual étale extensions and removal of absent boundary components. -/

section

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FormallyEtale R S]

/-- Extension of a logarithmic derivation preserves the actual extended boundary ideals. -/
theorem extendEtaleRingDerivation_logarithmic (w : ι → R) (D : LogarithmicDerivation.Construction.logarithmicDerivations w) :
    Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D.val ∈
      LogarithmicDerivation.Construction.logarithmicDerivations (fun i => algebraMap R S (w i)) := by
  intro i
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (D.property i)
  rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, ht, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem firstLogarithmicDifferentialIdeal_map_le (w : ι → R) (J : Ideal R) :
    (LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal w J).map (algebraMap R S) ≤
      LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal (fun i => algebraMap R S (w i)) (J.map (algebraMap R S)) := by
  rw [Ideal.map_le_iff_le_comap]
  apply sup_le
  · intro p hp
    exact LogarithmicBoundaryReindex.Construction.le_firstLogarithmicDifferentialIdeal _ _ (Ideal.mem_map_of_mem _ hp)
  · apply Ideal.span_le.mpr
    rintro x ⟨⟨D, p⟩, rfl⟩
    change algebraMap R S (D.val p.val) ∈
      LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal (fun i => algebraMap R S (w i)) (J.map (algebraMap R S))
    rw [← Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (S := S) D.val p.val]
    exact LogarithmicBoundaryReindex.Construction.logarithmic_derivation_mem_first _ _
      ⟨Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D.val, extendEtaleRingDerivation_logarithmic w D⟩
      (Ideal.mem_map_of_mem _ p.property)

theorem iteratedLogarithmicDifferentialIdeal_map_le (w : ι → R) (J : Ideal R) (n : ℕ) :
    (LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n).map (algebraMap R S) ≤
      LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal (fun i => algebraMap R S (w i))
        (J.map (algebraMap R S)) n := by
  induction n generalizing J with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal w J)).trans
      (LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal_mono _ n (firstLogarithmicDifferentialIdeal_map_le (S := S) w J))

/-- Logarithmic unit-ideal bounds persist under actual formally étale maps,
including localization at a point or on an affine open. -/
theorem logarithmic_order_bound_map (w : ι → R) (J : Ideal R) (n : ℕ)
    (h : LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n = ⊤) :
    LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal (fun i => algebraMap R S (w i))
      (J.map (algebraMap R S)) n = ⊤ := by
  have hle := iteratedLogarithmicDifferentialIdeal_map_le (S := S) w J n
  rw [h, Ideal.map_top] at hle
  exact top_le_iff.mp hle

end

variable {R σ : Type*} [CommRing R] [DecidableEq σ]

/-- Boundary equations that are units impose no logarithmic tangency condition. -/
theorem logarithmicDerivations_remove_unit_components (w : σ → R) (B C : Finset σ)
    (hCB : C ⊆ B) (hunit : ∀ i ∈ B, i ∉ C → IsUnit (w i)) :
    LogarithmicDerivation.Construction.logarithmicDerivations (fun i : B => w i.val) = LogarithmicDerivation.Construction.logarithmicDerivations (fun i : C => w i.val) := by
  ext D
  constructor
  · intro h i
    exact h ⟨i.val, hCB i.property⟩
  · intro h i
    by_cases hi : i.val ∈ C
    · exact h ⟨i.val, hi⟩
    · change D (w i.val) ∈ Ideal.span {w i.val}
      rw [Ideal.span_singleton_eq_top.mpr (hunit i.val i.property hi)]
      exact Submodule.mem_top

end

/-! A logarithmic unit-ideal bound rules out residual boundary factors, including locally. -/

variable {R ι : Type*} [CommRing R]

/-- Preserving a boundary generator's principal ideal implies preserving
every section of that ideal. -/
theorem logarithmic_derivation_preserves_boundary_ideal (w : ι → R)
    (D : LogarithmicDerivation.Construction.logarithmicDerivations w) (i : ι) (p : R) (hp : p ∈ Ideal.span {w i}) :
    D.val p ∈ Ideal.span {w i} := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hp
  rw [ht, D.val.leibniz]
  change w i * D.val t + t * D.val (w i) ∈ Ideal.span {w i}
  exact (Ideal.span {w i}).add_mem
    ((Ideal.span {w i}).mul_mem_right _ (Ideal.mem_span_singleton_self _))
    ((Ideal.span {w i}).mul_mem_left t (D.property i))

theorem firstLogarithmicDifferentialIdeal_preserves_boundary (w : ι → R)
    (J : Ideal R) (i : ι) (hJ : J ≤ Ideal.span {w i}) :
    LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal w J ≤ Ideal.span {w i} := by
  apply sup_le hJ
  apply Ideal.span_le.mpr
  rintro p ⟨⟨D, q⟩, rfl⟩
  exact logarithmic_derivation_preserves_boundary_ideal w D i q.val (hJ q.property)

theorem iteratedLogarithmicDifferentialIdeal_preserves_boundary (w : ι → R)
    (J : Ideal R) (i : ι) (n : ℕ) (hJ : J ≤ Ideal.span {w i}) :
    LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n ≤ Ideal.span {w i} := by
  induction n generalizing J with
  | zero => exact hJ
  | succ n ih =>
    exact ih (LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal w J)
      (firstLogarithmicDifferentialIdeal_preserves_boundary w J i hJ)

/-- A logarithmic unit-ideal bound prevents divisibility by any proper boundary equation. -/
theorem logarithmic_order_bound_excludes_boundary_factor (w : ι → R) (J : Ideal R) (n : ℕ)
    (hbound : LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n = ⊤)
    (i : ι) (hi : Ideal.span {w i} ≠ ⊤) : ¬ J ≤ Ideal.span {w i} := by
  intro hJ
  have hle := iteratedLogarithmicDifferentialIdeal_preserves_boundary w J i n hJ
  rw [hbound] at hle
  exact hi (top_le_iff.mp hle)

/-- The exclusion holds in the actual local ring at every point of a
boundary component. Thus the preserved logarithmic bound already prevents
new residual divisibility by that component. -/
theorem logarithmic_order_bound_excludes_local_boundary_factor (w : ι → R) (J : Ideal R) (n : ℕ)
    (hbound : LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n = ⊤)
    (q : Ideal R) [q.IsPrime] (i : ι) (hi : w i ∈ q) :
    ¬ J.map (algebraMap R (Localization.AtPrime q)) ≤
      Ideal.span {algebraMap R (Localization.AtPrime q) (w i)} := by
  let T := Localization.AtPrime q
  let : Algebra.FormallyEtale R T := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have hlog := logarithmic_order_bound_map (S := T) w J n hbound
  apply logarithmic_order_bound_excludes_boundary_factor _ _ n hlog i
  have himem : algebraMap R T (w i) ∈ IsLocalRing.maximalIdeal T := by
    change w i ∈ (IsLocalRing.maximalIdeal T).under R
    rw [Localization.AtPrime.under_maximalIdeal (I := q)]
    exact hi
  have hle := (Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal T)).mpr himem
  intro ht
  rw [ht] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_le_iff.mp hle)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicEtaleMap.Construction
