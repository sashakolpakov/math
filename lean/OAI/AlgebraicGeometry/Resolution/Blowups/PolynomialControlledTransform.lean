import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Filtration
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Polynomial Controlled Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialControlledTransform.Construction

noncomputable section

/-! Existence of polynomial controlled transforms from center-order bounds. -/

open _root_.Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The chart substitution induced by `φ` on coefficients and `z = c z'`. -/
def scaledPolynomialMap (φ : R →+* S) (c : S) : R[X] →+* S[X] :=
  (compRingHom (C c * X)).comp (mapRingHom φ)

theorem scaledPolynomialMap_apply (φ : R →+* S) (c : S) (p : R[X]) :
    scaledPolynomialMap φ c p = (p.map φ).comp (C c * X) := rfl

/-- A regular element remains regular when regarded as a constant polynomial. -/
theorem polynomial_C_regular (c : S) (hc : IsRegular c) : IsRegular (C c) := by
  have hl : IsLeftRegular (C c : S[X]) := by
    intro p q h
    ext j
    apply hc.left
    simpa only [coeff_C_mul] using congrArg (fun f : S[X] => f.coeff j) h
  exact ⟨hl, fun p q h => hl (by simpa only [mul_comm _ (C c)] using h)⟩

/-- If the coefficient-center ideal becomes divisible by `c`, the entire
center `(I,z)` becomes divisible by the exceptional constant polynomial. -/
theorem scaledPolynomialMap_center_le (I : Ideal R) (φ : R →+* S) (c : S)
    (hI : I.map φ ≤ Ideal.span {c}) :
    (Coefficient.Filtration.Construction.polynomialCenterIdeal I).map (scaledPolynomialMap φ c) ≤ Ideal.span {C c} := by
  rw [Ideal.map_le_iff_le_comap]
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change (scaledPolynomialMap φ c) (C r) ∈ Ideal.span {C c}
    rw [scaledPolynomialMap_apply, map_C, C_comp]
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hI (Ideal.mem_map_of_mem φ hr))
    apply Ideal.mem_span_singleton.mpr
    exact ⟨C d, by rw [← map_mul, hd]⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    change (scaledPolynomialMap φ c) X ∈ Ideal.span {C c}
    rw [scaledPolynomialMap_apply, map_X, X_comp]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (C c)))

/-- A center-order bound guarantees existence and uniqueness of the
polynomial obtained by dividing out the specified exceptional power. -/
theorem existsUnique_polynomialControlledTransform
    (I : Ideal R) (φ : R →+* S) (c : S) (hc : IsRegular c)
    (hI : I.map φ ≤ Ideal.span {c}) (p : R[X]) (b : ℕ)
    (hp : p ∈ Coefficient.Filtration.Construction.polynomialCenterIdeal I ^ b) :
    ∃! q : S[X], (p.map φ).comp (C c * X) = C (c ^ b) * q := by
  have hm : (Coefficient.Filtration.Construction.polynomialCenterIdeal I ^ b).map (scaledPolynomialMap φ c) ≤
      Ideal.span {C (c ^ b)} := by
    rw [Ideal.map_pow, map_pow, ← Ideal.span_singleton_pow]
    exact pow_le_pow_left' (scaledPolynomialMap_center_le I φ c hI) b
  have hmem := hm (Ideal.mem_map_of_mem (scaledPolynomialMap φ c) hp)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  exact (polynomial_C_regular (c ^ b) (hc.pow b)).left (hq'.symm.trans hq)

/-- The transform exists in the polynomial ring over each actual blowup
chart of the coefficient center. -/
theorem blowupChart_existsUnique_polynomialControlledTransform
    (I : Ideal R) (a : I) (p : R[X]) (b : ℕ)
    (hp : p ∈ Coefficient.Filtration.Construction.polynomialCenterIdeal I ^ b) :
    ∃! q : (Blowup.Charts.Construction.blowupChart I a)[X],
      (p.map (Blowup.Charts.Construction.blowupChartConstants I a)).comp (C (Blowup.Charts.Construction.blowupChartConstants I a a.val) * X) =
        C ((Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b) * q :=
  existsUnique_polynomialControlledTransform I (Blowup.Charts.Construction.blowupChartConstants I a)
    (Blowup.Charts.Construction.blowupChartConstants I a a.val) (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
    (ExceptionalIdeal.Construction.blowupChart_extendedIdeal I a).le p b hp

/-- The constructed transform has the expected coefficient and derivative
transformation laws, with no transform-existence assumption. -/
theorem blowupChart_exists_polynomialControlledTransform_with_formulas
    (I : Ideal R) (a : I) (p : R[X]) (b : ℕ)
    (hp : p ∈ Coefficient.Filtration.Construction.polynomialCenterIdeal I ^ b) :
    ∃ q : (Blowup.Charts.Construction.blowupChart I a)[X],
      (p.map (Blowup.Charts.Construction.blowupChartConstants I a)).comp (C (Blowup.Charts.Construction.blowupChartConstants I a a.val) * X) =
        C ((Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b) * q ∧
      (∀ j ≤ b, Blowup.Charts.Construction.blowupChartConstants I a (p.coeff j) =
        (Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ (b - j) * q.coeff j) ∧
      (∀ k ≤ b,
        ((derivative^[k] p).map (Blowup.Charts.Construction.blowupChartConstants I a)).comp
            (C (Blowup.Charts.Construction.blowupChartConstants I a a.val) * X) =
          C ((Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ (b - k)) * derivative^[k] q) := by
  obtain ⟨q, hq, _⟩ := blowupChart_existsUnique_polynomialControlledTransform I a p b hp
  refine ⟨q, hq, ?_, ?_⟩
  · intro j hj
    exact ResidualCoefficientTransform.Construction.coefficient_controlledTransform _ p q _ b j
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a) hj hq
  · intro k hk
    exact ResidualCoefficientTransform.Construction.iteratedDerivative_controlledTransform _ p q _ b k
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a) hk hq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialControlledTransform.Construction
