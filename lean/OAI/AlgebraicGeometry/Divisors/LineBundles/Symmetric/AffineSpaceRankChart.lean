import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasisRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSchemeIso

/-! # Affine Space Rank Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSpaceRankChart.BundleCycles

noncomputable section

/-! The polynomial chart of a projective symmetric spectrum has exactly
the module's rank at the chosen prime. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem projectiveSymmetric_exists_affineSpaceChart_of_rank {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    (p : PrimeSpectrum R) (n : ℕ) (hp : Module.rankAtStalk M p = n) :
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ (ι : Type) (_ : Finite ι)
      (e : Spec (.of (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r))) ≅
        AffineSpace ι (Spec (.of (Localization.Away r)))),
      e.hom ≫ (AffineSpace ι (Spec (.of (Localization.Away r))) ↘ Spec (.of (Localization.Away r))) =
        PrincipalChart.BundleCycles.symmetricPrincipalChartProjection M r ∧ Nat.card ι = n := by
  obtain ⟨r, hr, ι, hι, b, hn⟩ := LineBundles.Projective.ModuleLocalBasisRank.BundleCycles.projectiveModule_exists_localBasis_of_rank M p n hp
  let := hι
  let S := Localization.Away r
  let m := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  let e := (LocalizationEquiv.BundleCycles.symmetricLocalizationEquiv M (Submonoid.powers r) S m).trans
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv
  have he : ∀ a : S, e (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) S a) = MvPolynomial.C a := by
    intro a
    change (SymmetricAlgebra.equivMvPolynomial b)
      (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) (Submonoid.powers r) m
        (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) S a)) = _
    rw [LocalizationEquiv.BundleCycles.symmetricLocalizationMap_scalar]
    exact (SymmetricAlgebra.equivMvPolynomial b).commutes a
  exact ⟨r, hr, ι, hι, AffineSchemeIso.BundleCycles.symmetricPolynomialChartEquiv M r e,
    AffineSchemeIso.BundleCycles.symmetricPolynomialChartEquiv_over M r e he, hn⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSpaceRankChart.BundleCycles
