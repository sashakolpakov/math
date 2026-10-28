import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.PrincipalChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasis
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Affine Scheme Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSchemeIso.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: polynomial trivializations as actual affine-space charts over the coefficient scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (r : R) {ι : Type}

def symmetricPolynomialChartEquiv
    (e : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r) ≃+* MvPolynomial ι (Localization.Away r)) :
    Spec (.of (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r))) ≅
      AffineSpace ι (Spec (.of (Localization.Away r))) :=
  Scheme.Spec.mapIso e.symm.toCommRingCatIso.op ≪≫ (AffineSpace.SpecIso ι (.of (Localization.Away r))).symm

theorem symmetricPolynomialChartEquiv_over
    (e : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r) ≃+* MvPolynomial ι (Localization.Away r))
    (he : ∀ a : Localization.Away r,
      e (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) (Localization.Away r) a) = MvPolynomial.C a) :
    (symmetricPolynomialChartEquiv M r e).hom ≫
      (AffineSpace ι (Spec (.of (Localization.Away r))) ↘ Spec (.of (Localization.Away r))) =
      PrincipalChart.BundleCycles.symmetricPrincipalChartProjection M r := by
  have h : (CommRingCat.ofHom (MvPolynomial.C : Localization.Away r →+* MvPolynomial ι _)) ≫
      e.symm.toCommRingCatIso.hom =
        CommRingCat.ofHom (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) (Localization.Away r)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact e.symm_apply_eq.mpr (he a).symm
  change (Spec.map e.symm.toCommRingCatIso.hom ≫
    (AffineSpace.SpecIso ι (.of (Localization.Away r))).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, h]
  rfl

variable [Module.Projective R M] [Module.Finite R M]

theorem projectiveSymmetric_exists_affineSpaceChart (p : Ideal R) [p.IsPrime] :
    ∃ (r : R), r ∉ p ∧ ∃ (ι : Type) (_ : Finite ι)
      (e : Spec (.of (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r))) ≅
        AffineSpace ι (Spec (.of (Localization.Away r)))),
      e.hom ≫ (AffineSpace ι (Spec (.of (Localization.Away r))) ↘ Spec (.of (Localization.Away r))) =
        PrincipalChart.BundleCycles.symmetricPrincipalChartProjection M r := by
  obtain ⟨r, hr, ι, hι, e, he⟩ := LineBundles.Projective.ModuleLocalBasis.BundleCycles.projectiveSymmetric_exists_trivialization M p
  exact ⟨r, hr, ι, hι, symmetricPolynomialChartEquiv M r e,
    symmetricPolynomialChartEquiv_over M r e he⟩

end

/-! A basis identifies the actual affine symmetric spectrum with
relative affine space over the same coefficient ring. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M)

def symmetricAffineSchemeIso : Spec (.of (SymmetricAlgebra R M)) ≅ AffineSpace ι (Spec (.of R)) :=
  Scheme.Spec.mapIso (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso ι (.of R)).symm

theorem symmetricAffineSchemeIso_over :
    (symmetricAffineSchemeIso b).hom ≫ (AffineSpace ι (Spec (.of R)) ↘ Spec (.of R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))) := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  have he : CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial ι R) ≫
      e.symm.toRingEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M)) := by
    ext r
    exact e.symm.commutes r
  change (Spec.map e.symm.toRingEquiv.toCommRingCatIso.hom ≫ (AffineSpace.SpecIso ι (.of R)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, he]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSchemeIso.BundleCycles
