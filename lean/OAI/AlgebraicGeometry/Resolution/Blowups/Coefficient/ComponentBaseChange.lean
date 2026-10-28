import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientNaturality

/-! # Component Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange.Construction

noncomputable section

/-! Canonical ambient coefficient component centers commute with actual étale refinements. -/

universe u

theorem aligned_quotient_preimage_map {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) (w : S) (h : f z = w) (K : Ideal (R ⧸ Ideal.span {z})) :
    (K.comap (Ideal.Quotient.mk (Ideal.span {z}))).map f =
      (K.map (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f z w h)).comap (Ideal.Quotient.mk (Ideal.span {w})) := by
  let I := K.comap (Ideal.Quotient.mk (Ideal.span {z}))
  have hzI : z ∈ I := by
    change Ideal.Quotient.mk (Ideal.span {z}) z ∈ K
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)]
    exact K.zero_mem
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {w})) ≤ I.map f := by
    rw [Ideal.mk_ker]
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [← h]
    exact Ideal.mem_map_of_mem f hzI
  have hm : (I.map f).map (Ideal.Quotient.mk (Ideal.span {w})) = K.map (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f z w h) := by
    rw [← CenterDescent.Construction.alignedHypersurfaceMap_ideal_map f z w h I,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hrec := Ideal.comap_map_of_surjective (Ideal.Quotient.mk (Ideal.span {w}))
    Ideal.Quotient.mk_surjective (I.map f)
  rw [hm, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at hrec
  exact hrec.symm

theorem smooth_relativeCoefficientIdeal_map_aligned
    (k : Type u) {R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (z : R) (w : S) (h : f z = w) (J : Ideal R) (b : ℕ) :
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z w h) =
      Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k w (J.map f.toRingHom) b := by
  unfold Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  apply congrArg (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b)
  funext j
  rw [Ideal.map_map]
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map
    ((Ideal.Quotient.mk (Ideal.span {w})).comp f.toRingHom) = _
  rw [← Ideal.map_map, Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf]

theorem coefficientComponentCenter_map_etale
    (k : Type u) {R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (z : R)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] (J : Ideal R) (b : ℕ) :
    (ComponentNaturality.Construction.coefficientComponentCenter k z J b).map f.toRingHom =
      ComponentNaturality.Construction.coefficientComponentCenter k (f z) (J.map f.toRingHom) b := by
  unfold ComponentNaturality.Construction.coefficientComponentCenter
  rw [aligned_quotient_preimage_map f.toRingHom z (f z) rfl]
  have hm := DifferentialSaturation.Construction.relativeDifferentialSaturation_map k (TangentNaturality.Construction.alignedHypersurfaceAlgHom f z (f z) rfl)
    (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale f.toRingHom hf z (f z) rfl) (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b)
  change (DifferentialSaturation.Construction.relativeDifferentialSaturation k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b)).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
    DifferentialSaturation.Construction.relativeDifferentialSaturation k ((Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl)) at hm
  rw [hm, smooth_relativeCoefficientIdeal_map_aligned k f hf z (f z) rfl]

theorem smooth_relativeHomogenizedIdeal_map
    (k : Type u) {R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (J : Ideal R) (n : ℕ) :
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom = Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map f.toRingHom) n := by
  unfold Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal
  simp only [Ideal.map_iSup, Ideal.map_mul, Ideal.map_pow, Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf]

theorem homogenized_coefficientComponentCenter_map_etale
    (k : Type u) {R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (z : R)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] (J : Ideal R) (n : ℕ) :
    (ComponentNaturality.Construction.coefficientComponentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)).map f.toRingHom =
      ComponentNaturality.Construction.coefficientComponentCenter k (f z) (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map f.toRingHom) n) (n + 1) := by
  rw [coefficientComponentCenter_map_etale k f hf, smooth_relativeHomogenizedIdeal_map k f hf]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange.Construction
