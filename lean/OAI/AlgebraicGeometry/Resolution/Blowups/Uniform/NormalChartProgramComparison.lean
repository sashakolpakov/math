import OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalChartOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalChartIntrinsicData
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CarrierOverlapPointedComparison

/-! # Normal Chart Program Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Actual programs on two modeled normal charts have a common program at every order-locus overlap point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram.openComparisonAt_of_global_normal_charts
    {d : ℕ} {𝒮 : ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y Y' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {x x' : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x) (C' : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x')
    [IsDomain C.chart.ring] [IsIntegral C.chart.nativeCarrier.subscheme] [IsIntegral C'.chart.nativeCarrier.subscheme]
    [Smooth (C.chart.nativeCarrier.subschemeι ≫ (C.chart.map ≫ f))]
    [Smooth (C'.chart.nativeCarrier.subschemeι ≫ (C'.chart.map ≫ f))]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec C.chart.ring) (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) Y g K}
    {P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec C'.chart.ring) (C'.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C'.chart.map) Y' g' K'}
    (A : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) C.chart.nativeCarrier
      (fun l => (D l).comap C.chart.map) P)
    (A' : CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule (C'.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C'.chart.map) C'.chart.nativeCarrier
      (fun l => (D l).comap C'.chart.map) P')
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) (n + 1) C.chart.nativeCarrier.subschemeι ≠ ⊥)
    (hC' : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (C'.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C'.chart.map) (n + 1) C'.chart.nativeCarrier.subschemeι ≠ ⊥)
    (hd : topologicalKrullDim C.chart.nativeCarrier.subscheme ≤ d)
    (hd' : topologicalKrullDim C'.chart.nativeCarrier.subscheme ≤ d)
    (p : Spec C.chart.ring) (q : Spec C'.chart.ring) (hpq : C.chart.map p = C'.chart.map q)
    (hp : C.chart.map p ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    P.OpenComparisonAt P' C.chart.map C'.chart.map p q := by
  let : IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C.chart.normal})).subscheme :=
    inferInstanceAs (IsIntegral C.chart.nativeCarrier.subscheme)
  let : IsIntegral (Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {C'.chart.normal})).subscheme :=
    inferInstanceAs (IsIntegral C'.chart.nativeCarrier.subscheme)
  let : Smooth (C.chart.nativeCarrier.subschemeι ≫ (C.chart.map ≫ f)) := C.chart.nativeCarrier_smooth
  let : Smooth (C'.chart.nativeCarrier.subschemeι ≫ (C'.chart.map ≫ f)) := C'.chart.nativeCarrier_smooth
  have hex : ∃ B : TangentCarrierData.Construction.TangentCarrierOverlapData (C.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C.chart.map) C.chart.nativeCarrier
      (fun l => (D l).comap C.chart.map) (C'.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap C'.chart.map) C'.chart.nativeCarrier
      (fun l => (D l).comap C'.chart.map) n,
      ∃ z : B.ambient, B.left z = p ∧ B.right z = q ∧ B.left ≫ C.chart.map = B.right ≫ C'.chart.map := by
    rw [C.chart.ground, C'.chart.ground, C.chart.homogenized_restrict, C'.chart.homogenized_restrict,
      funext C.chart.component, funext C'.chart.component]
    exact Global.NormalChartOverlap.Construction.exists_tangent_overlap_of_global_normal_charts C C' p q hpq hp
  obtain ⟨B, z, hz, hz', hcomm⟩ := hex
  exact A.openComparisonAt_of_overlap_data A' hC hC' hd hd' C.chart.nativeCarrier_tangent
    B C.chart.map C'.chart.map hcomm p q z hz hz'

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
