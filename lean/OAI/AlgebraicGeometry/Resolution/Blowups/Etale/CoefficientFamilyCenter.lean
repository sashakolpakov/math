import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedCenterQuotient
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCenterChart

/-! # Coefficient Family Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientFamilyCenter.Construction

noncomputable section

/-! Retained normal coefficient families imply ambient permissibility on actual étale charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem etale_coefficient_family_center_permissible
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I J H : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (hHI : H ≤ I)
    (C : H.subscheme.IdealSheafData) (b : ℕ) (hC : C ≤ (I.comap H.subschemeι) ^ b.factorial)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (A : Ideal R) (hA : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel A)
    (z : R) (hHz : H.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z}))
    (D : Derivation ℂ R R) (hD : D z = 1) {τ : Type} (p : τ → R)
    (hp : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span (Set.range p)))
    (l : Spec (.of (R ⧸ Ideal.span {z})) ⟶ H.subscheme)
    (hl : l ≫ H.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {z}))) ≫ j)
    (C₀ : Ideal (R ⧸ Ideal.span {z})) (hC₀ : C.comap l = Affine.QuotientKernel.Construction.affineQuotientKernel C₀)
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C₀) :
    J.comap j ≤ (I ^ b).comap j := by
  let : Algebra ℚ R := ((algebraMap ℂ R).comp (algebraMap ℚ ℂ)).toAlgebra
  have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hj ▸ inferInstanceAs (Smooth (j ≫ f))
  let : Algebra.Smooth ℂ R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap ℂ R))).mp hs)
  let : Algebra.Smooth ℂ (R ⧸ A) := ClosedCenterQuotient.Construction.idealSheaf_complex_center_quotient_on_etale_chart f I R j hj A hA
  have hzA : z ∈ A := by
    apply (Ideal.span_singleton_le_iff_mem A).mp
    apply (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp
    rw [← hHz, ← hA]
    exact Scheme.IdealSheafData.comap_mono j hHI
  have hbound : C₀ ≤ (A.map (Ideal.Quotient.mk (Ideal.span {z}))) ^ b.factorial := by
    apply (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp
    rw [Affine.QuotientKernel.Construction.affineQuotientKernel_pow, ← hC₀]
    have he : (I.comap H.subschemeι).comap l =
        Affine.QuotientKernel.Construction.affineQuotientKernel (A.map (Ideal.Quotient.mk (Ideal.span {z}))) := by
      rw [← Scheme.IdealSheafData.comap_comp, hl, Scheme.IdealSheafData.comap_comp, hA,
        Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
    rw [← he, ← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
    exact Scheme.IdealSheafData.comap_mono l hC
  rw [hp, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, hA, ← Affine.QuotientKernel.Construction.affineQuotientKernel_pow]
  exact (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mpr ((Blowups.Smooth.CoefficientFamilyCenter.Construction.smooth_center_iff_weighted_normal_family ℂ A z hzA D hD p b).mpr
    (hlow.trans hbound))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientFamilyCenter.Construction
