import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicAffineBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterModelRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LogarithmicTransform

/-! # Logarithmic Blowup Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The intrinsic global logarithmic order bound survives actual boundary-compatible blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_bound_on_model
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type} {D : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ)
    (hbound : A.logarithmicIdeal J n = ⊤) (U : X.affineOpens) (w : β → Γ(X, U))
    (hw : ∀ l, (D l).ideal U = Ideal.span {w l})
    (M : letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U; Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ Γ(X, U) β w) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ w (J.ideal U) n = ⊤ := by
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hD (l : β) : (D l).comap U.2.fromSpec = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w l}) := by
    rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, hw l]
  have he := A.logarithmicIdeal_restrict_etale J n (.of Γ(X, U)) U.2.fromSpec
    (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm w hD M (J.ideal U)
    (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel J U)
  rw [hbound, Scheme.IdealSheafData.comap_top] at he
  apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
  rw [DifferentialUnitGluing.Construction.affineQuotientKernel_top]
  exact he.symm

theorem Global.LogarithmicBlowupBound.Construction.globalBlowup_preserves_logarithmic_order_bound
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (B' : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D))
    (m : ℕ) (hp : J ≤ I ^ m) (hbound : B.logarithmicIdeal J m = ⊤) :
    B'.logarithmicIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) m = ⊤ := by
  obtain ⟨N, hN⟩ := A.exists_model_refinement
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ (N.reesCover hI).openCover
  intro p
  change (i : N.indices) × I.ideal (N.opens i) at p
  let U := N.opens p.1
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let w := N.equations p.1
  let F := N.divided p.1
  let hw := N.contained p.1
  obtain ⟨M⟩ := hN p.1
  have hb := B.logarithmicIdeal_bound_on_model J m hbound U w (N.component p.1) M
  let v := MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) p.2 F w hw
  have hB : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) p.2)) v :=
    MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, U)) (I.ideal U) w F hw
      (N.boundary p.1) (N.center p.1) p.2
  have ht := MixedBoundary.LogarithmicTransform.Construction.blowup_mixed_boundary_preserves_relative_logarithmic_bound ℂ
    (I.ideal U) (J.ideal U) p.2 F w hw m (hp U) hb
  change (B'.logarithmicIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) m).comap
    (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U p.2) = ⊤
  exact B'.logarithmicIdeal_unit_on_affine (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) m
    (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) p.2)) (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U p.2)
    (GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f I hI U p.2) v
    (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_comap_reesChart I hI D F U w (N.component p.1) hw p.2 hB)
    hB (ControlledTransform.Construction.blowupControlledTransform (I.ideal U) (J.ideal U) m p.2)
    (GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart I J hI m U p.2) ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups
