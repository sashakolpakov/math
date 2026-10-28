import OAI.AlgebraicGeometry.Resolution.Blowups.TwoTransverseTangentComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafCongruence

/-! # Intrinsic Affine Tangent Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicAffineTangentComparison.Construction

noncomputable section

/-! The constructed change of maximal contact gives actual pointed scheme maps, with native ideal and tangent congruence identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_native_affine_tangent_comparison
    {σ R : Type} [CommRing R] [Algebra ℂ R] [Algebra ℚ R]
    [Algebra (MvPolynomial σ ℂ) R] [Algebra.Etale (MvPolynomial σ ℂ) R]
    [IsScalarTower ℂ (MvPolynomial σ ℂ) R] [Fintype σ] [DecidableEq σ]
    (J : Ideal R) (B : Finset σ) (z t : R) (n : ℕ) (p : PrimeSpectrum R)
    (hp : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n ≤ p.asIdeal)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n) (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n)
    (htransz : ∃ i : σ, i ∉ B ∧ Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := ℂ) (S := R) i z ∉ p.asIdeal)
    (htranst : ∃ i : σ, i ∉ B ∧ Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := ℂ) (S := R) i t ∉ p.asIdeal) :
    ∃ (S : CommRingCat) (_ : Algebra ℂ S), ∃ a b : Spec S ⟶ Spec (.of R),
      Etale a ∧ Etale b ∧ a ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S ∧
      b ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S ∧
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ J n)).comap a =
        (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ J n)).comap b ∧
      (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})).comap a =
        (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t})).comap b ∧
      (∀ i ∈ B, (Affine.QuotientKernel.Construction.affineQuotientKernel
        (Ideal.span {algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i)})).comap a =
        (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i)})).comap b) ∧
      IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent a b (Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n)) ∧
      ∃ q : PrimeSpectrum S, a q = p ∧ b q = p := by
  let r : R →ₐ[ℂ] p.asIdeal.ResidueField := IsScalarTower.toAlgHom ℂ R p.asIdeal.ResidueField
  have htz : ∃ i : σ, i ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := ℂ) (S := R) i z) ≠ 0 := by
    obtain ⟨i, hi, hd⟩ := htransz
    exact ⟨i, hi, fun he => hd (Ideal.algebraMap_residueField_eq_zero.mp he)⟩
  have htt : ∃ i : σ, i ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := ℂ) (S := R) i t) ≠ 0 := by
    obtain ⟨i, hi, hd⟩ := htranst
    exact ⟨i, hi, fun he => hd (Ideal.algebraMap_residueField_eq_zero.mp he)⟩
  have hpoint : r z = r t :=
    (Ideal.algebraMap_residueField_eq_zero.mpr (hp hz)).trans
      (Ideal.algebraMap_residueField_eq_zero.mpr (hp ht)).symm
  obtain ⟨S, instS, algS, F, G, v, hF, hG, heq, hB, hJ, hvF, hvG, hT, hdiff, _⟩ :=
    TwoTransverseTangentComparison.Construction.exists_two_transverse_equation_tangent_comparison J B z t n r htz htt hz ht hpoint
  let a := Spec.map (CommRingCat.ofHom F.toRingHom)
  let b := Spec.map (CommRingCat.ofHom G.toRingHom)
  let q : PrimeSpectrum S := ⟨RingHom.ker v.toRingHom, Ideal.comap_isPrime v.toRingHom ⊥⟩
  refine ⟨.of S, algS, a, b,
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hF,
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hG, ?_, ?_, ?_, ?_, ?_,
    Affine.IdealSheafCongruence.Construction.idealSheafCongruent_Spec_of_congruence F.toRingHom G.toRingHom _ hT hdiff, q, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom F.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (RingHom.ext F.commutes)
  · change Spec.map (CommRingCat.ofHom G.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (RingHom.ext G.commutes)
  · rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, hJ]
  · rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    exact congrArg (fun v : S => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v})) heq
  · intro i hi
    rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    exact congrArg (fun v : S => Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v})) (hB i hi)
  · apply PrimeSpectrum.ext
    ext x
    change v (F x) = 0 ↔ x ∈ p.asIdeal
    rw [hvF]
    exact Ideal.algebraMap_residueField_eq_zero
  · apply PrimeSpectrum.ext
    ext x
    change v (G x) = 0 ↔ x ∈ p.asIdeal
    rw [hvG]
    exact Ideal.algebraMap_residueField_eq_zero

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicAffineTangentComparison.Construction
