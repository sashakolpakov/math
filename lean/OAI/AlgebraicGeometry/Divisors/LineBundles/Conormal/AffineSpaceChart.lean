import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SupportPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSchemeIso

/-! # Affine Space Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.AffineSpaceChart.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual conormal principal charts are finite affine spaces over their base opens -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.AffineZariskiSite)
    [Module.Projective (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent]
    [Module.Finite (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent]

theorem conormal_exists_affineSpaceChart (q : PrimeSpectrum (Γ(X, U.1) ⧸ I.ideal U)) :
    ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ I.subscheme) (ι : Type) (_ : Finite ι)
      (j : AffineSpace ι (Spec B) ⟶ DiagramGluing.BundleCycles.globalConormalSpectrum I),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ Support.Projection.BundleCycles.supportCoefficientChart I U q ∈ Set.range i ∧
      IsPullback (AffineSpace ι (Spec B) ↘ Spec B) j i (SupportCover.BundleCycles.globalConormalToSupport I) := by
  obtain ⟨r, hr, ι, hι, e, he⟩ := Symmetric.AffineSchemeIso.BundleCycles.projectiveSymmetric_exists_affineSpaceChart
    (I.ideal U).Cotangent q.asIdeal
  let B : CommRingCat := .of (Localization.Away r)
  let i := SupportPullback.BundleCycles.conormalPrincipalChartToSupport I U r
  let j := e.inv ≫ SupportPullback.BundleCycles.conormalPrincipalChartInclusion I U r
  have hi : IsOpenImmersion i := SupportPullback.BundleCycles.conormalPrincipalChartToSupport_isOpenImmersion I U r
  have hj : IsOpenImmersion j := by
    have := SupportPullback.BundleCycles.conormalPrincipalChartInclusion_isOpenImmersion I U r
    exact IsOpenImmersion.comp e.inv (SupportPullback.BundleCycles.conormalPrincipalChartInclusion I U r)
  refine ⟨B, i, ι, hι, j, hi, hj, ?_, ?_⟩
  · have hq : q ∈ Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap (Γ(X, U.1) ⧸ I.ideal U) (Localization.Away r)))) := by
      have hRange : Set.range (Spec.map (CommRingCat.ofHom
          (algebraMap (Γ(X, U.1) ⧸ I.ideal U) (Localization.Away r)))) =
          (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (Γ(X, U.1) ⧸ I.ideal U))) :=
        PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
      exact (congrArg (fun A : Set (PrimeSpectrum (Γ(X, U.1) ⧸ I.ideal U)) => q ∈ A) hRange).mpr hr
    obtain ⟨q', hq'⟩ := hq
    exact ⟨q', congrArg (Support.Projection.BundleCycles.supportCoefficientChart I U) hq'⟩
  · apply (SupportPullback.BundleCycles.conormalPrincipalChart_isPullback I U r).of_iso e (.refl _) (.refl _) (.refl _)
    · exact (Category.comp_id _).trans he.symm
    · change _ ≫ 𝟙 _ = e.hom ≫ (e.inv ≫ _)
      rw [Category.comp_id, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.AffineSpaceChart.BundleCycles
