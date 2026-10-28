import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange

/-! # Tangent Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentBaseChange.Construction

noncomputable section

/-! Fixed-level intrinsic coefficient tangent centers commute with actual étale refinements. -/

universe u

theorem coefficientTangentCenter_map_etale
    (k : Type u) {R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (z : R)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] (J : Ideal R) (b ℓ : ℕ) :
    (TangentNaturality.Construction.coefficientTangentCenter k z J b ℓ).map f.toRingHom =
      TangentNaturality.Construction.coefficientTangentCenter k (f z) (J.map f.toRingHom) b ℓ := by
  unfold TangentNaturality.Construction.coefficientTangentCenter
  rw [ComponentBaseChange.Construction.aligned_quotient_preimage_map f.toRingHom z (f z) rfl]
  have hm := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k (TangentNaturality.Construction.alignedHypersurfaceAlgHom f z (f z) rfl)
    (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale f.toRingHom hf z (f z) rfl) (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) ℓ
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) ℓ).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k ((Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl)) ℓ at hm
  rw [hm, ComponentBaseChange.Construction.smooth_relativeCoefficientIdeal_map_aligned k f hf z (f z) rfl]

theorem homogenized_coefficientTangentCenter_map_etale
    (k : Type u) {R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (z : R)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] (J : Ideal R) (n ℓ : ℕ) :
    (TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ).map f.toRingHom =
      TangentNaturality.Construction.coefficientTangentCenter k (f z) (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map f.toRingHom) n) (n + 1) ℓ := by
  rw [coefficientTangentCenter_map_etale k f hf, ComponentBaseChange.Construction.smooth_relativeHomogenizedIdeal_map k f hf]

theorem homogenized_coefficient_bound_map_etale
    (k : Type u) {R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale) (z : R)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] (J : Ideal R) (n m : ℕ)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (f z) (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map f.toRingHom) n) (n + 1)) m = ⊤ := by
  have hcenter : TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) m = ⊤ := by
    unfold TangentNaturality.Construction.coefficientTangentCenter
    rw [hbound, Ideal.comap_top]
  have hm := homogenized_coefficientTangentCenter_map_etale k f hf z J n m
  rw [hcenter, Ideal.map_top] at hm
  have hq := TangentNaturality.Construction.coefficientTangentCenter_quotient k (f z)
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map f.toRingHom) n) (n + 1) m
  rw [← hm, Ideal.map_top] at hq
  exact hq.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentBaseChange.Construction
