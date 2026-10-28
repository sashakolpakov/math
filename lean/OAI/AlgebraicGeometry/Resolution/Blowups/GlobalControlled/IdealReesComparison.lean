import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFactorization

/-! # Ideal Rees Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.IdealReesComparison.Construction

noncomputable section

/-! Every actual Rees comparison over an affine chart carries the exact native controlled ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupControlledIdeal_comap_rees_comparison
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) (hp : J ≤ I ^ b)
    (R : CommRingCat) (j : Spec R ⟶ X) (A B : Ideal R)
    (hA : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel A) (hB : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel B)
    (a : A) (j' : Spec (.of (Blowup.Charts.Construction.blowupChart A a)) ⟶ GlobalBlowup.Data.Construction.globalBlowup I hI)
    (hover : j' ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI =
      Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants A a)) ≫ j) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap j' =
      Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform A B b a) := by
  change (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap j' = Affine.QuotientKernel.Construction.affineQuotientKernel
    ((B.map (Blowup.Charts.Construction.blowupChartConstants A a)).colon (Ideal.span {Blowup.Charts.Construction.blowupChartConstants A a a.val ^ b}))
  apply Locally.PrincipalColonFactorization.Construction.idealSheaf_factorization_comap_regular_affine (J.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI))
    ((I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)
    (Factorization.Construction.globalBlowup_controlledIdeal_factorization I J hI b hp) (.of (Blowup.Charts.Construction.blowupChart A a)) j'
      (B.map (Blowup.Charts.Construction.blowupChartConstants A a)) (Blowup.Charts.Construction.blowupChartConstants A a a.val ^ b)
  · rw [← Scheme.IdealSheafData.comap_comp, hover, Scheme.IdealSheafData.comap_comp,
      hB, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  · rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, ← Scheme.IdealSheafData.comap_comp, hover,
      Scheme.IdealSheafData.comap_comp, hA, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      ← Affine.QuotientKernel.Construction.affineQuotientKernel_pow, ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.span_singleton_pow]
  · exact IsRegular.pow (a := Blowup.Charts.Construction.blowupChartConstants A a a.val) b
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular A a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.IdealReesComparison.Construction
