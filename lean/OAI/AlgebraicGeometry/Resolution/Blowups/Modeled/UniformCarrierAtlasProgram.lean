import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.NormalChartProgramComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.TangentPrefixDescent

/-! # Uniform Carrier Atlas Program -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasProgram.Construction

/-! A global homogenized program retains its actual modeled normal atlas and every intrinsic coefficient program. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure ModeledUniformCarrierAtlasProgram
    {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (schedule : 𝒮.Schedule (n + 1).factorial β)
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (D : β → X.IdealSheafData)
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y g K) where
  indices : Type
  finite : Fintype indices
  nonempty : Nonempty indices
  point : indices → X
  chart : ∀ i, GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D (point i)
  domain : ∀ i, IsDomain (chart i).chart.ring
  carrierIntegral : ∀ i, IsIntegral (chart i).chart.nativeCarrier.subscheme
  carrierDimension : ∀ i, topologicalKrullDim (chart i).chart.nativeCarrier.subscheme ≤ d
  cover : ∀ x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support, ∃ i p, (chart i).chart.map p = x
  coefficientNonzero : ∀ i, GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf ((chart i).chart.map ≫ f)
    ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap (chart i).chart.map) (n + 1)
      (chart i).chart.nativeCarrier.subschemeι ≠ ⊥
  endpoint : indices → Scheme
  structureMap : ∀ i, endpoint i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  ideal : ∀ i, (endpoint i).IdealSheafData
  localPrefix : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec (chart i).chart.ring) ((chart i).chart.map ≫ f)
    ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap (chart i).chart.map) (endpoint i) (structureMap i) (ideal i)
  certificate : ∀ i, letI : Smooth ((chart i).chart.nativeCarrier.subschemeι ≫ ((chart i).chart.map ≫ f)) :=
    (chart i).chart.nativeCarrier_smooth
    Uniform.CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule ((chart i).chart.map ≫ f)
    ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap (chart i).chart.map) (chart i).chart.nativeCarrier
      (fun l => (D l).comap (chart i).chart.map) (localPrefix i)
  comparisonMap : ∀ i, endpoint i ⟶ Y
  comparison : ∀ i, P.EtaleComparison (localPrefix i) (chart i).chart.map (comparisonMap i)
  trace : P.HasIncidenceTrace β D (𝒮.incidenceTrace schedule)
  terminal : letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤

attribute [instance] ModeledUniformCarrierAtlasProgram.finite ModeledUniformCarrierAtlasProgram.nonempty
  ModeledUniformCarrierAtlasProgram.domain ModeledUniformCarrierAtlasProgram.carrierIntegral

end AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasProgram.Construction

namespace AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram

/-! A shared coefficient schedule determines the whole global program independently of the modeled normal atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_endpointIso
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y Y' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {K : Y.IdealSheafData} {K' : Y'.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y g K}
    {P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y' g' K'}
    (A : ModeledUniformCarrierAtlasProgram 𝒮 schedule f J D P)
    (B : ModeledUniformCarrierAtlasProgram 𝒮 schedule f J D P') :
    ∃ e : Y' ≅ Y, P.EtaleComparison P' (𝟙 X) e.hom ∧
      ∀ r : Y' ⟶ Y, P.EtaleComparison P' (𝟙 X) r → r = e.hom := by
  have hN : P.stepCount = P'.stepCount :=
    (A.trace.stepCount P D (𝒮.incidenceTrace schedule)).trans (B.trace.stepCount P' D (𝒮.incidenceTrace schedule)).symm
  apply P.exists_endpointIso_of_pointed_tangent P' hN
  intro x hx
  rw [Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_tangent] at hx
  obtain ⟨i, p, hp⟩ := A.cover x hx
  obtain ⟨a, q, hq⟩ := B.cover x hx
  let : Smooth ((A.chart i).chart.nativeCarrier.subschemeι ≫ ((A.chart i).chart.map ≫ f)) :=
    (A.chart i).chart.nativeCarrier_smooth
  let : Smooth ((B.chart a).chart.nativeCarrier.subschemeι ≫ ((B.chart a).chart.map ≫ f)) :=
    (B.chart a).chart.nativeCarrier_smooth
  obtain ⟨S, W, s, w, L, M, R, c, d, r, t, z, hc, hd, hcomm, hleft, hright⟩ :=
    (A.certificate i).openComparisonAt_of_global_normal_charts (A.chart i) (B.chart a) (B.certificate a)
      (A.coefficientNonzero i) (B.coefficientNonzero a) (A.carrierDimension i) (B.carrierDimension a)
      p q (hp.trans hq.symm) (hp.symm ▸ hx)
  have hP := (A.comparison i).comp P (A.localPrefix i) (A.chart i).chart.map (A.comparisonMap i)
    R c r hleft
  have hP' := (B.comparison a).comp P' (B.localPrefix a) (B.chart a).chart.map (B.comparisonMap a)
    R d t hright
  refine ⟨S, W, s, w, L, M, R, c ≫ (A.chart i).chart.map, d ≫ (B.chart a).chart.map,
    r ≫ A.comparisonMap i, t ≫ B.comparisonMap a, z, ?_, ?_, hP, hP'⟩
  · change (A.chart i).chart.map (c z) = x
    rw [hc, hp]
  · rw [hcomm]
    exact ⟨rfl, rfl⟩

end AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram

end

end OAI
