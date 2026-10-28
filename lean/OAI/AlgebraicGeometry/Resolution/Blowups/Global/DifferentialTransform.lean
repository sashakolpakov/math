import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.DifferentialBound
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Differential Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform.Construction

noncomputable section

/-! Global relative differential filtration under actual controlled transforms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineQuotientKernel_mono {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I ≤ J) : Affine.QuotientKernel.Construction.affineQuotientKernel I ≤ Affine.QuotientKernel.Construction.affineQuotientKernel J := by
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop, Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop]
  exact Ideal.comap_mono h

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

omit [Smooth f] in
/-- On every actual Rees chart, the global differential ideal of the
controlled transform is the kernel sheaf of the algebraic differential ideal. -/
theorem globalBlowupControlledIdeal_differential_comap_reesChart
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (b r : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (U : X.affineOpens) (a : I.ideal U) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) r).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) =
        Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ
          (ControlledTransform.Construction.blowupControlledTransform (I.ideal U) (J.ideal U) b a) r) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let j := GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a
  let g := GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f
  have he : j ≫ g = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (Blowup.Charts.Construction.blowupChart (I.ideal U) a) :=
    GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f I hI U a
  have hsmooth : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (Blowup.Charts.Construction.blowupChart (I.ideal U) a)) :=
    he ▸ (inferInstanceAs (Smooth (j ≫ g)))
  let : Algebra.Smooth ℂ (Blowup.Charts.Construction.blowupChart (I.ideal U) a) := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsmooth)
  rw [Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open,
    GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart]
  exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (j ≫ g) _ he _ r).trans
    (ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel _ _ r)

theorem globalBlowup_relativeDifferential_controlled_le_on_chart
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (n r : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (hperm : J ≤ I ^ (n + r))
    (U : X.affineOpens) (a : I.ideal U) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r) hI n).comap
      (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) ≤
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + r)) r).comap
          (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart,
    globalBlowupControlledIdeal_differential_comap_reesChart]
  apply affineQuotientKernel_mono
  exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le ℂ
    (I.ideal U) (J.ideal U) a n r (hperm U)

/-- The relative differential filtration satisfies its full controlled
transform inclusion for the native global ideal sheaves. -/
theorem globalBlowup_relativeDifferential_controlled_le
    (I J : X.IdealSheafData) (hI : I ≠ ⊥) (n r : ℕ)
    [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] (hperm : J ≤ I ^ (n + r)) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J r) hI n ≤
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + r)) r := by
  exact IdealSheaf.EqualityGluing.Construction.idealSheaf_le_of_openCover _ _ (GlobalControlled.Chart.Construction.globalBlowupReesAffineCover I hI).openCover
    (fun p => globalBlowup_relativeDifferential_controlled_le_on_chart f I J hI n r hperm p.1 p.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform.Construction
