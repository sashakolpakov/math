import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.QuotientTorBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport

/-! # Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Order

noncomputable section

/-! Native orders of vanishing under flat local base change. If the
maximal ideal extends to the maximal ideal, all rational-function orders
are preserved under the compatible fraction-field embedding. -/

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]

theorem ord_baseChange (a : R) :
    Ring.ord S (algebraMap R S a) = Ring.ord R a *
      Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  have hi : Ideal.span {algebraMap R S a} = (Ideal.span {a}).map (algebraMap R S) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [Ring.ord, hi, (Ideal.qoutMapEquivTensorQout (R := R) (I := Ideal.span {a}) S).length_eq]
  exact IsLocalRing.length_baseChange R S _

theorem ord_eq (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (a : R) : Ring.ord S (algebraMap R S a) = Ring.ord R a := by
  rw [ord_baseChange, hmax, SurfacePrimeEuler.residue_quotient_length, mul_one]

variable [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
  [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]

omit [IsNoetherianRing S] [Ring.KrullDimLE 1 S] in
theorem ordMonoid_eq
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (hinj : Function.Injective (algebraMap R S)) (a : R) :
    Ring.ordMonoidWithZeroHom S (algebraMap R S a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · subst a
    simp only [map_zero]
  have ha' : algebraMap R S a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hR : Ring.ord R a = ((Ring.ord R a).toNat : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm
  have hS := (ord_eq R S hmax a).trans hR
  rw [Ring.ordMonoidWithZeroHom_eq_coe S (mem_nonZeroDivisors_of_ne_zero ha') hS,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero ha) hR]

theorem ordFrac_eq {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (hinj : Function.Injective (algebraMap R S)) (φ : K →+* L)
    (hφ : ∀ a : R, φ (algebraMap R K a) = algebraMap S L (algebraMap R S a)) (f : K) :
    Ring.ordFrac S (φ f) = Ring.ordFrac R f := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [map_div₀, hφ a, hφ b, map_div₀, map_div₀,
    Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb',
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ hinj).mpr ha),
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ hinj).mpr hb'),
    ordMonoid_eq R S hmax hinj a, ordMonoid_eq R S hmax hinj b]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Order
