import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.CoefficientSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ComponentGluing

/-! # Affine Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.AffineCharts.Construction

noncomputable section

/-! Exact affine formulas for the intrinsic coefficient sheaf on actual closed carriers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothDifferentialIdealSheaf_comap_affine
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    {R : Type} [CommRing R] [Algebra ℂ R] (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K : Ideal R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K) :
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap j =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ K n) := by
  have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hj ▸ (inferInstanceAs (Smooth (j ≫ f)))
  let : Algebra.Smooth ℂ R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)
  rw [Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open, hK]
  exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (j ≫ f) _ hj _ n).trans
    (ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel R K n)

theorem smoothCoefficientIdealSheaf_comap_quotient_chart
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X)
    {R : Type} [CommRing R] [Algebra ℂ R] (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K L : Ideal R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (l : Spec (.of (R ⧸ L)) ⟶ Y)
    (hcomm : l ≫ q = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L)) ≫ j) :
    (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q).comap l =
      Affine.QuotientKernel.Construction.affineQuotientKernel (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b
        (fun r => (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ K r.val).map (Ideal.Quotient.mk L))) := by
  rw [CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_comap]
  simp only [CoefficientSheaf.Construction.smoothCoefficientIdealSheaf, hcomm, Scheme.IdealSheafData.comap_comp]
  simp_rw [smoothDifferentialIdealSheaf_comap_affine f J _ j hj K hK, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  simp only [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal, Affine.KernelSums.Construction.affineQuotientKernel_iSup, Affine.QuotientKernel.Construction.affineQuotientKernel_pow]

theorem smoothCoefficientIdealSheaf_comap_hypersurface_chart
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X)
    {R : Type} [CommRing R] [Algebra ℂ R] (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K : Ideal R) (z : R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (l : Spec (.of (R ⧸ Ideal.span {z})) ⟶ Y)
    (hcomm : l ≫ q = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {z}))) ≫ j) :
    (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q).comap l = Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal ℂ z K b) :=
  smoothCoefficientIdealSheaf_comap_quotient_chart f J b q j hj K (Ideal.span {z}) hK l hcomm

theorem smoothCoefficientIdealSheaf_subschemeChart
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (b : ℕ) (U : X.affineOpens) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    (CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι).comap (H.subschemeCover.f U) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b
        (fun r => (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (J.ideal U) r.val).map (Ideal.Quotient.mk (H.ideal U)))) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  apply smoothCoefficientIdealSheaf_comap_quotient_chart f J b H.subschemeι U.2.fromSpec
    (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm (J.ideal U) (H.ideal U)
    (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel J U) (H.subschemeCover.f U)
  exact (Scheme.IdealSheafData.subschemeCover_map_subschemeι H U).trans (Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.AffineCharts.Construction
