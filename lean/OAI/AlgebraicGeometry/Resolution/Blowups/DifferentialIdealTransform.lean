import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialBlowupTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Differential Ideal Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialIdealTransform.Construction

noncomputable section

/-! Differential ideals and their compatibility with controlled transforms. -/

universe u

variable {R : Type u} [CommRing R]

/-- Adjoin all first derivatives of sections of an ideal. -/
def firstDifferentialIdeal (J : Ideal R) : Ideal R :=
  J ⊔ Ideal.span (Set.range (fun t : Derivation ℤ R R × J => t.1 t.2.val))

theorem le_firstDifferentialIdeal (J : Ideal R) : J ≤ firstDifferentialIdeal J := le_sup_left

theorem derivation_mem_firstDifferentialIdeal (J : Ideal R) (D : Derivation ℤ R R)
    {p : R} (hp : p ∈ J) : D p ∈ firstDifferentialIdeal J :=
  (show Ideal.span _ ≤ firstDifferentialIdeal J from le_sup_right)
    (Ideal.subset_span ⟨⟨D, ⟨p, hp⟩⟩, rfl⟩)

theorem firstDifferentialIdeal_mono {J K : Ideal R} (h : J ≤ K) :
    firstDifferentialIdeal J ≤ firstDifferentialIdeal K := by
  apply sup_le
  · exact h.trans (le_firstDifferentialIdeal K)
  · apply Ideal.span_le.mpr
    rintro r ⟨⟨D, p⟩, rfl⟩
    exact derivation_mem_firstDifferentialIdeal K D (h p.property)

theorem firstDifferentialIdeal_le_pow (I J : Ideal R) (n : ℕ) (hJ : J ≤ I ^ (n + 1)) :
    firstDifferentialIdeal J ≤ I ^ n := by
  apply sup_le
  · exact hJ.trans (Ideal.pow_le_pow_right (by omega))
  · apply Ideal.span_le.mpr
    rintro r ⟨⟨D, p⟩, rfl⟩
    exact DifferentialOrder.Construction.derivation_mem_pow D I n (hJ p.property)

/-- Iterating the first differential ideal includes derivatives of all
orders up to the specified bound, together with their ideal combinations. -/
def iteratedDifferentialIdeal (J : Ideal R) : ℕ → Ideal R
  | 0 => J
  | n + 1 => iteratedDifferentialIdeal (firstDifferentialIdeal J) n

theorem iteratedDifferentialIdeal_mono (n : ℕ) {J K : Ideal R} (h : J ≤ K) :
    Construction.iteratedDifferentialIdeal J n ≤ Construction.iteratedDifferentialIdeal K n := by
  induction n generalizing J K with
  | zero => exact h
  | succ n ih => exact ih (firstDifferentialIdeal_mono h)

theorem iteratedDifferentialIdeal_le_pow (I J : Ideal R) (n k : ℕ)
    (hJ : J ≤ I ^ (n + k)) : Construction.iteratedDifferentialIdeal J k ≤ I ^ n := by
  induction k generalizing J with
  | zero => simpa [Construction.iteratedDifferentialIdeal] using hJ
  | succ k ih =>
    apply ih
    apply firstDifferentialIdeal_le_pow I J (n + k)
    simpa only [Nat.add_assoc] using hJ

/-- Each original section has a divided section lying in the controlled ideal. -/
theorem blowup_controlledTransform_section_exists (I J : Ideal R) (a : I) (b : ℕ)
    (hJ : J ≤ I ^ b) (p : J) :
    ∃ q : Blowup.Charts.Construction.blowupChart I a, q ∈ ControlledTransform.Construction.blowupControlledTransform I J b a ∧
      Blowup.Charts.Construction.blowupChartConstants I a p.val = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b * q := by
  obtain ⟨q, hq, _⟩ := ControlledTransform.Construction.blowup_controlledTransform_unique_division I J b a hJ p
  refine ⟨q, ?_, hq.symm⟩
  apply Ideal.mem_colon_span_singleton.mpr
  change q * Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b ∈ J.map (Blowup.Charts.Construction.blowupChartConstants I a)
  rw [mul_comm q (Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b), hq]
  exact Ideal.mem_map_of_mem _ p.property

/-- The control-`n` transform of the first differential ideal is contained
in the first differential ideal of the control-`n+1` transform. -/
theorem firstDifferentialIdeal_controlledTransform_le (I J : Ideal R) (a : I) (n : ℕ)
    (hJ : J ≤ I ^ (n + 1)) :
    ControlledTransform.Construction.blowupControlledTransform I (firstDifferentialIdeal J) n a ≤
      firstDifferentialIdeal (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  let T := ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a
  let U := firstDifferentialIdeal T
  have htotal : (firstDifferentialIdeal J).map (Blowup.Charts.Construction.blowupChartConstants I a) ≤
      Ideal.span {c ^ n} * U := by
    rw [Ideal.map_le_iff_le_comap]
    apply sup_le
    · intro p hp
      obtain ⟨q, hq, he⟩ := blowup_controlledTransform_section_exists I J a (n + 1) hJ ⟨p, hp⟩
      change Blowup.Charts.Construction.blowupChartConstants I a p ∈ Ideal.span {c ^ n} * U
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨c * q, U.mul_mem_left c (le_firstDifferentialIdeal T hq), ?_⟩
      calc
        c ^ n * (c * q) = c ^ (n + 1) * q := by
          rw [pow_succ c]
          exact (mul_assoc (c ^ n) c q).symm
        _ = Blowup.Charts.Construction.blowupChartConstants I a p := he.symm
    · apply Ideal.span_le.mpr
      rintro r ⟨⟨D, p⟩, rfl⟩
      obtain ⟨q, hq, he⟩ := blowup_controlledTransform_section_exists I J a (n + 1) hJ p
      change Blowup.Charts.Construction.blowupChartConstants I a (D p.val) ∈ Ideal.span {c ^ n} * U
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨ChartDerivation.Construction.blowupChartDerivation I a D q +
        (n + 1 : ℕ) * Blowup.Charts.Construction.blowupChartConstants I a (D a.val) * q, ?_,
        (DifferentialBlowupTransform.Construction.blowupChart_derivative_division I a D n p.val q he).symm⟩
      apply Ideal.add_mem
      · exact derivation_mem_firstDifferentialIdeal T (ChartDerivation.Construction.blowupChartDerivation I a D) hq
      · exact U.mul_mem_left _ (le_firstDifferentialIdeal T hq)
  have hcolon := Submodule.colon_mono htotal (Set.Subset.refl (Ideal.span {c ^ n} : Set _))
  have hc : IsRegular c := ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a
  have hcn : IsRegular (c ^ n) := IsRegular.pow (a := c) n hc
  have heq : (Ideal.span {c ^ n} * U).colon (Ideal.span {c ^ n}) = U :=
    ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular U (c ^ n) hcn
  rw [heq] at hcolon
  exact hcolon

/-- Differential ideals commute with controlled transformation in the
inclusion direction needed for persistence of maximal contact. -/
theorem iteratedDifferentialIdeal_controlledTransform_le
    (I J : Ideal R) (a : I) (n k : ℕ) (hJ : J ≤ I ^ (n + k)) :
    ControlledTransform.Construction.blowupControlledTransform I (Construction.iteratedDifferentialIdeal J k) n a ≤
      Construction.iteratedDifferentialIdeal (ControlledTransform.Construction.blowupControlledTransform I J (n + k) a) k := by
  induction k generalizing J with
  | zero => simp [Construction.iteratedDifferentialIdeal]
  | succ k ih =>
    have hJ' : J ≤ I ^ (n + k + 1) := by simpa only [Nat.add_assoc] using hJ
    have hfirst := firstDifferentialIdeal_controlledTransform_le I J a (n + k) hJ'
    have hind := ih (firstDifferentialIdeal J) (firstDifferentialIdeal_le_pow I J (n + k) hJ')
    exact hind.trans (by
      simpa only [Construction.iteratedDifferentialIdeal, Nat.add_assoc] using
        iteratedDifferentialIdeal_mono k hfirst)

/-- A hypersurface equation belonging to the control-one differential ideal
retains that property after each actual chart blowup. This form can be iterated. -/
theorem blowupChart_differential_hypersurface_persists
    (I J : Ideal R) (a z : I) (k : ℕ) (hJ : J ≤ I ^ (k + 1))
    (hz : z.val ∈ Construction.iteratedDifferentialIdeal J k) :
    ExceptionalIdeal.Construction.blowupChartRatio I a z ∈
      Construction.iteratedDifferentialIdeal (ControlledTransform.Construction.blowupControlledTransform I J (k + 1) a) k := by
  have h := iteratedDifferentialIdeal_controlledTransform_le I J a 1 k
    (by simpa only [Nat.add_comm 1 k] using hJ)
  apply (by simpa only [Nat.add_comm 1 k] using h)
  apply Ideal.mem_colon_span_singleton.mpr
  change ExceptionalIdeal.Construction.blowupChartRatio I a z * Blowup.Charts.Construction.blowupChartConstants I a a.val ^ 1 ∈
    (Construction.iteratedDifferentialIdeal J k).map (Blowup.Charts.Construction.blowupChartConstants I a)
  rw [pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val),
    mul_comm (ExceptionalIdeal.Construction.blowupChartRatio I a z) (Blowup.Charts.Construction.blowupChartConstants I a a.val),
    ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio]
  exact Ideal.mem_map_of_mem _ hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialIdealTransform.Construction
