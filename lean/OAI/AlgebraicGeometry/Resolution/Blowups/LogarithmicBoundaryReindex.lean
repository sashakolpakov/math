import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicDerivation
import OAI.AlgebraicGeometry.Resolution.Blowups.MaximumOrderTransform

/-! # Logarithmic Boundary Reindex -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicBoundaryReindex.Construction

noncomputable section

section

/-! Logarithmic differential ideals and their actual controlled transforms. -/

variable {R ι : Type*} [CommRing R]

/-- Adjoin first derivatives taken only in directions preserving every boundary ideal. -/
def firstLogarithmicDifferentialIdeal (w : ι → R) (J : Ideal R) : Ideal R :=
  J ⊔ Ideal.span (Set.range (fun t : LogarithmicDerivation.Construction.logarithmicDerivations w × J => t.1.val t.2.val))

theorem le_firstLogarithmicDifferentialIdeal (w : ι → R) (J : Ideal R) :
    J ≤ firstLogarithmicDifferentialIdeal w J := le_sup_left

theorem logarithmic_derivation_mem_first (w : ι → R) (J : Ideal R)
    (D : LogarithmicDerivation.Construction.logarithmicDerivations w) {p : R} (hp : p ∈ J) :
    D.val p ∈ firstLogarithmicDifferentialIdeal w J :=
  (show Ideal.span _ ≤ firstLogarithmicDifferentialIdeal w J from le_sup_right)
    (Ideal.subset_span ⟨⟨D, ⟨p, hp⟩⟩, rfl⟩)

theorem firstLogarithmicDifferentialIdeal_mono (w : ι → R) {J L : Ideal R} (h : J ≤ L) :
    firstLogarithmicDifferentialIdeal w J ≤ firstLogarithmicDifferentialIdeal w L := by
  apply sup_le
  · exact h.trans (le_firstLogarithmicDifferentialIdeal w L)
  · apply Ideal.span_le.mpr
    rintro x ⟨⟨D, p⟩, rfl⟩
    exact logarithmic_derivation_mem_first w L D (h p.property)

theorem firstLogarithmicDifferentialIdeal_le_ordinary (w : ι → R) (J : Ideal R) :
    firstLogarithmicDifferentialIdeal w J ≤ DifferentialIdealTransform.Construction.firstDifferentialIdeal J := by
  apply sup_le
  · exact DifferentialIdealTransform.Construction.le_firstDifferentialIdeal J
  · apply Ideal.span_le.mpr
    rintro x ⟨⟨D, p⟩, rfl⟩
    exact DifferentialIdealTransform.Construction.derivation_mem_firstDifferentialIdeal J D.val p.property

def iteratedLogarithmicDifferentialIdeal (w : ι → R) (J : Ideal R) : ℕ → Ideal R
  | 0 => J
  | n + 1 => iteratedLogarithmicDifferentialIdeal w (firstLogarithmicDifferentialIdeal w J) n

theorem iteratedLogarithmicDifferentialIdeal_mono (w : ι → R) (n : ℕ)
    {J L : Ideal R} (h : J ≤ L) :
    Construction.iteratedLogarithmicDifferentialIdeal w J n ≤ Construction.iteratedLogarithmicDifferentialIdeal w L n := by
  induction n generalizing J L with
  | zero => exact h
  | succ n ih => exact ih (firstLogarithmicDifferentialIdeal_mono w h)

theorem iteratedLogarithmicDifferentialIdeal_le_ordinary (w : ι → R) (J : Ideal R) (n : ℕ) :
    Construction.iteratedLogarithmicDifferentialIdeal w J n ≤ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n := by
  induction n generalizing J with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (firstLogarithmicDifferentialIdeal w J)).trans
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_mono n (firstLogarithmicDifferentialIdeal_le_ordinary w J))

/-- The first logarithmic differential transform is contained in the first
logarithmic differential ideal of the transformed ideal, with the new
exceptional equation included among the boundary equations. -/
theorem firstLogarithmicDifferentialIdeal_controlledTransform_le
    (I J : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (n : ℕ) (hJ : J ≤ I ^ (n + 1)) :
    ControlledTransform.Construction.blowupControlledTransform I (firstLogarithmicDifferentialIdeal w J) n a ≤
      firstLogarithmicDifferentialIdeal
        (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w')
        (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  let T := ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a
  let W : Option ι → Blowup.Charts.Construction.blowupChart I a := fun i => Option.elim i c w'
  let U := firstLogarithmicDifferentialIdeal W T
  have htotal : (firstLogarithmicDifferentialIdeal w J).map (Blowup.Charts.Construction.blowupChartConstants I a) ≤
      Ideal.span {c ^ n} * U := by
    rw [Ideal.map_le_iff_le_comap]
    apply sup_le
    · intro p hp
      obtain ⟨q, hq, heq⟩ := DifferentialIdealTransform.Construction.blowup_controlledTransform_section_exists I J a (n + 1) hJ ⟨p, hp⟩
      change Blowup.Charts.Construction.blowupChartConstants I a p ∈ Ideal.span {c ^ n} * U
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨c * q, U.mul_mem_left c (le_firstLogarithmicDifferentialIdeal W T hq), ?_⟩
      calc
        c ^ n * (c * q) = c ^ (n + 1) * q := by rw [pow_succ c]; exact (mul_assoc (c ^ n) c q).symm
        _ = Blowup.Charts.Construction.blowupChartConstants I a p := heq.symm
    · apply Ideal.span_le.mpr
      rintro r ⟨⟨D, p⟩, rfl⟩
      obtain ⟨q, hq, heq⟩ := DifferentialIdealTransform.Construction.blowup_controlledTransform_section_exists I J a (n + 1) hJ p
      change Blowup.Charts.Construction.blowupChartConstants I a (D.val p.val) ∈ Ideal.span {c ^ n} * U
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨ChartDerivation.Construction.blowupChartDerivation I a D.val q +
        (n + 1 : ℕ) * Blowup.Charts.Construction.blowupChartConstants I a (D.val a.val) * q, ?_,
        (DifferentialBlowupTransform.Construction.blowupChart_derivative_division I a D.val n p.val q heq).symm⟩
      apply Ideal.add_mem
      · exact logarithmic_derivation_mem_first W T
          ⟨ChartDerivation.Construction.blowupChartDerivation I a D.val, LogarithmicDerivation.Construction.blowupChartDerivation_logarithmic I a w w' e he D⟩ hq
      · exact U.mul_mem_left _ (le_firstLogarithmicDifferentialIdeal W T hq)
  have hcolon := Submodule.colon_mono htotal (Set.Subset.refl (Ideal.span {c ^ n} : Set _))
  have hc : IsRegular (c ^ n) := IsRegular.pow (a := c) n (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
  rw [ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular U (c ^ n) hc] at hcolon
  exact hcolon

/-- The logarithmic transform inclusion iterates with the same boundary
family on each side, so it preserves finite differential order bounds. -/
theorem iteratedLogarithmicDifferentialIdeal_controlledTransform_le
    (I J : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (n k : ℕ) (hJ : J ≤ I ^ (n + k)) :
    ControlledTransform.Construction.blowupControlledTransform I (Construction.iteratedLogarithmicDifferentialIdeal w J k) n a ≤
      Construction.iteratedLogarithmicDifferentialIdeal
        (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w')
        (ControlledTransform.Construction.blowupControlledTransform I J (n + k) a) k := by
  induction k generalizing J with
  | zero => simp only [Construction.iteratedLogarithmicDifferentialIdeal, Nat.add_zero, le_refl]
  | succ k ih =>
    have hJ' : J ≤ I ^ (n + k + 1) := by simpa only [Nat.add_assoc] using hJ
    have hfirst := firstLogarithmicDifferentialIdeal_controlledTransform_le I J a w w' e he (n + k) hJ'
    have hlog : firstLogarithmicDifferentialIdeal w J ≤ I ^ (n + k) :=
      (firstLogarithmicDifferentialIdeal_le_ordinary w J).trans
        (DifferentialIdealTransform.Construction.firstDifferentialIdeal_le_pow I J (n + k) hJ')
    have hind := ih (firstLogarithmicDifferentialIdeal w J) hlog
    exact hind.trans (by
      simpa only [Construction.iteratedLogarithmicDifferentialIdeal, Nat.add_assoc] using
        iteratedLogarithmicDifferentialIdeal_mono _ k hfirst)

/-- A logarithmic unit-ideal bound survives every actual controlled blowup,
including the addition of the new exceptional component to the boundary. -/
theorem blowup_preserves_logarithmic_order_bound
    (I J : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (m : ℕ) (hJ : J ≤ I ^ m) (hbound : Construction.iteratedLogarithmicDifferentialIdeal w J m = ⊤) :
    Construction.iteratedLogarithmicDifferentialIdeal
      (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w')
      (ControlledTransform.Construction.blowupControlledTransform I J m a) m = ⊤ := by
  have h := iteratedLogarithmicDifferentialIdeal_controlledTransform_le I J a w w' e he 0 m
    (by simpa only [zero_add] using hJ)
  rw [zero_add, hbound, ResidualCoefficientTransform.Construction.blowupControlledTransform_zero, Ideal.map_top] at h
  exact top_le_iff.mp h

end

/-! Logarithmic ideals depend on the boundary conditions, including removal of empty components. -/

variable {R ι κ : Type*} [CommRing R]

/-- Equal modules of boundary-preserving derivations give equal iterated
logarithmic differential ideals, regardless of the boundary index set. -/
theorem iteratedLogarithmicDifferentialIdeal_congr_derivations
    (w : ι → R) (v : κ → R) (h : LogarithmicDerivation.Construction.logarithmicDerivations w = LogarithmicDerivation.Construction.logarithmicDerivations v)
    (J : Ideal R) (n : ℕ) :
    Construction.iteratedLogarithmicDifferentialIdeal w J n = Construction.iteratedLogarithmicDifferentialIdeal v J n := by
  have hfirst (L : Ideal R) : firstLogarithmicDifferentialIdeal w L = firstLogarithmicDifferentialIdeal v L := by
    unfold firstLogarithmicDifferentialIdeal
    rw [h]
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    change Construction.iteratedLogarithmicDifferentialIdeal w (firstLogarithmicDifferentialIdeal w J) n = _
    rw [hfirst]
    exact ih (firstLogarithmicDifferentialIdeal v J)

variable {σ : Type*} [DecidableEq σ]

/-- Replace the old denominator component, whose divided equation is one,
by the new exceptional component. This gives precisely the coordinate
boundary indexed by `insert i B`. -/
theorem logarithmicDerivations_coordinate_boundary_reindex (x : σ → R) (B : Finset σ) (i : σ) :
    LogarithmicDerivation.Construction.logarithmicDerivations
      (fun j : Option B => Option.elim j (x i) (fun k => if k.val = i then 1 else x k.val)) =
      LogarithmicDerivation.Construction.logarithmicDerivations (fun j : (insert i B : Finset σ) => x j.val) := by
  ext D
  constructor
  · intro h j
    by_cases hji : j.val = i
    · change D (x j.val) ∈ Ideal.span {x j.val}
      rw [hji]
      exact h none
    · have hjB : j.val ∈ B := (Finset.mem_insert.mp j.property).resolve_left hji
      have hj := h (some ⟨j.val, hjB⟩)
      change D (if j.val = i then 1 else x j.val) ∈ Ideal.span {if j.val = i then 1 else x j.val} at hj
      rw [ite_eq_right hji] at hj
      exact hj
  · intro h j
    cases j with
    | none => exact h ⟨i, Finset.mem_insert_self i B⟩
    | some j =>
      change D (if j.val = i then 1 else x j.val) ∈ Ideal.span {if j.val = i then 1 else x j.val}
      by_cases hji : j.val = i
      · rw [ite_eq_left hji, D.map_one_eq_zero]
        exact Ideal.zero_mem _
      · rw [ite_eq_right hji]
        exact h ⟨j.val, Finset.mem_insert_of_mem j.property⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicBoundaryReindex.Construction
