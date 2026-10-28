import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientProgramPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ModeledNormalChartPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicCarrierRestriction

/-! # Normal Chart Program Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Transported modeled normal charts retain the intrinsic uniform program and its coefficient geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.exists_on_transported_normal_chart
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X V Y W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {x : X} (q : V ⟶ X) [Etale q] {y : V}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x)
    (B : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart (q ≫ f) (J.comap q) n (fun l => (D l).comap q) y)
    [IsIntegral C.chart.nativeCarrier.subscheme] [IsIntegral B.chart.nativeCarrier.subscheme]
    [Smooth (C.chart.nativeCarrier.subschemeι ≫ (C.chart.map ≫ f))]
    [Smooth (B.chart.nativeCarrier.subschemeι ≫ (B.chart.map ≫ (q ≫ f)))]
    (φ : C.chart.ring →ₐ[ℂ] B.chart.ring) (hφ : φ.toRingHom.Etale)
    (hcomm : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ C.chart.map = B.chart.map ≫ q)
    (hnormal : B.chart.normal = φ C.chart.normal)
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {M : W.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec C.chart.ring) (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) Y g K}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) C.chart.nativeCarrier
      (fun l => (D l).comap C.chart.map) P)
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) (n + 1) C.chart.nativeCarrier.subschemeι ≠ ⊥)
    (hd : topologicalKrullDim C.chart.nativeCarrier.subscheme ≤ d)
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec B.chart.ring) (B.chart.map ≫ (q ≫ f))
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n).comap B.chart.map) W k M)
    (r : W ⟶ Y) (hc : P.EtaleComparison Q (Spec.map (CommRingCat.ofHom φ.toRingHom)) r) :
    Nonempty (CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule (B.chart.map ≫ (q ≫ f))
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n).comap B.chart.map) B.chart.nativeCarrier
      (fun l => ((D l).comap q).comap B.chart.map) Q) ∧
      GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (B.chart.map ≫ (q ≫ f))
        ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n).comap B.chart.map) (n + 1)
          B.chart.nativeCarrier.subschemeι ≠ ⊥ ∧ topologicalKrullDim B.chart.nativeCarrier.subscheme ≤ d := by
  let a := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : Etale a := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hφ
  let : IsNoetherianRing B.chart.ring := Algebra.FiniteType.isNoetherianRing ℂ B.chart.ring
  let : IsLocallyNoetherian (Spec B.chart.ring) := inferInstance
  let : CompactSpace B.chart.nativeCarrier.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace B.chart.nativeCarrier.subschemeι
  have hg : a ≫ (C.chart.map ≫ f) = B.chart.map ≫ (q ≫ f) := by
    rw [← Category.assoc, hcomm, Category.assoc]
  have hJ : ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map).comap a =
      (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n).comap B.chart.map := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp,
      Global.HomogenizationEtalePullback.Construction.smoothHomogenizedIdealSheaf_comap_etale]
  have hH : C.chart.nativeCarrier.comap a = B.chart.nativeCarrier := by
    change (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})).comap
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {B.chart.normal})
    rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom, Ideal.map_span, Set.image_singleton, hnormal]
  have hD (l : β) : ((D l).comap C.chart.map).comap a = ((D l).comap q).comap B.chart.map := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomm, Scheme.IdealSheafData.comap_comp]
  have hA := A.exists_on_etale_comparison_to hC hd a (B.chart.map ≫ (q ≫ f))
    ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf (q ≫ f) (J.comap q) n).comap B.chart.map) B.chart.nativeCarrier hg hJ hH Q r hc
  rw [funext hD] at hA
  refine ⟨hA, ?_, ?_⟩
  · exact IntrinsicCarrierRestriction.Construction.native_carrier_restriction_coefficient_ne_bot (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) C.chart.nativeCarrier (n + 1) hC
      a (B.chart.map ≫ (q ≫ f)) _ B.chart.nativeCarrier hg hJ hH
  · exact Blowups.Etale.SchemeDimension.Construction.scheme_dimension_le_of_etale (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo C.chart.nativeCarrier B.chart.nativeCarrier a hH) d hd

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
