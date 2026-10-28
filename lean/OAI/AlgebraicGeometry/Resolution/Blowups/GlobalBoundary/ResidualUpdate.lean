import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AdmissibleMonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualBoundaryMonomialUpdate

/-! # Residual Update -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Exact global residual and boundary factor updates for every integral boundary-compatible center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem GlobalBoundary.ResidualUpdate.Construction.global_boundary_residual_factor_on_chart
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I M : X.IdealSheafData) (hI : I ≠ ⊥) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (F : Finset β) (a : β → ℕ) (m b : ℕ)
    (hperm : M ≤ I ^ (b - m)) (U : X.affineOpens)
    (w : β → Γ(X, U)) (hD : ∀ j, (D j).ideal U = Ideal.span {w j})
    (hM : M.ideal U = Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a})
    (hw : ∀ j ∈ F, w j ∈ I.ideal U) (d : I.ideal U)
    [Algebra ℂ Γ(X, U)]
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) d))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) d F w hw)) :
    (Global.CompanionTransform.Construction.globalResidualBoundaryFactorTransform I M hI m b).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) =
      (Global.MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b)).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) := by
  classical
  have hp : Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ I.ideal U ^ (b - m) := by
    rw [← hM]
    exact hperm U
  rw [Global.CompanionTransform.Construction.globalResidualBoundaryFactorTransform_comap_chart, hM, Global.MixedBoundary.Construction.boundaryMonomialSheaf_comap_open]
  simp_rw [CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_comap_reesChart I hI D F U w hD hw d hboundary]
  rw [Global.MixedBoundary.Construction.boundaryMonomialSheaf_affineQuotientKernel]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
    (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryFactorTransform_monomial (.of Γ(X, U)) (I.ideal U) d F w hw a m b hp hboundary)

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.residual_boundary_factor_integral_center
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData} [IsIntegral I.subscheme]
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (hI : I ≠ ⊥) (a : β → ℕ) (m b : ℕ) (hperm : Global.MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ (b - m)) :
    Global.CompanionTransform.Construction.globalResidualBoundaryFactorTransform I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI m b =
      Global.MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents (Global.AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D) a m b) := by
  let B := A.uniformIncidence
  let Q := B.reesCover hI
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ Q.openCover
  intro p
  let : Algebra ℂ Γ(X, B.opens p.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (B.opens p.1)
  exact GlobalBoundary.ResidualUpdate.Construction.global_boundary_residual_factor_on_chart I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI D
    (B.divided p.1) a m b hperm (B.opens p.1) (B.equations p.1) (B.component p.1)
    (Global.MixedBoundary.Construction.boundaryMonomialSheaf_local_equations D a (B.opens p.1) (B.equations p.1) (B.component p.1))
    (B.contained p.1) p.2
    (MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, B.opens p.1))
      (I.ideal (B.opens p.1)) (B.equations p.1) (B.divided p.1) (B.contained p.1)
      (B.boundary p.1) (B.center p.1) p.2)

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.residual_product_integral_center
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData} [IsIntegral I.subscheme]
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (J : X.IdealSheafData) (hI : I ≠ ⊥) (a : β → ℕ) (m b : ℕ)
    (hM : Global.MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ (b - m)) (hJ : J ≤ I ^ m) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b =
      Global.MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents (Global.AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D) a m b) *
          GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m := by
  rw [Global.CompanionTransform.Construction.globalBlowup_residual_product_transform I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) J hI m b hM hJ,
    A.residual_boundary_factor_integral_center hI a m b hM]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
