import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformCarrierAtlasProgram

/-! # Uniform Atlas Finite Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformAtlasFiniteRefinement.Construction

noncomputable section

section

/-! One pointed modeled chart retains its actual local program and its comparison to the global program. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure ModeledUniformChartProgram {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d)
    {n : ℕ} {β : Type} [Fintype β] [DecidableEq β] (schedule : 𝒮.Schedule (n + 1).factorial β)
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (D : β → X.IdealSheafData)
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y g K) (x : X) where
  chart : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x
  domain : IsDomain chart.chart.ring
  carrierIntegral : IsIntegral chart.chart.nativeCarrier.subscheme
  carrierDimension : topologicalKrullDim chart.chart.nativeCarrier.subscheme ≤ d
  coefficientNonzero : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (chart.chart.map ≫ f)
    ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap chart.chart.map) (n + 1) chart.chart.nativeCarrier.subschemeι ≠ ⊥
  endpoint : Scheme
  structureMap : endpoint ⟶ Foundations.Scheme.ProjectiveSpace.complexBase
  ideal : endpoint.IdealSheafData
  localPrefix : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (Spec chart.chart.ring) (chart.chart.map ≫ f)
    ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap chart.chart.map) endpoint structureMap ideal
  certificate : letI : Smooth (chart.chart.nativeCarrier.subschemeι ≫ (chart.chart.map ≫ f)) :=
    chart.chart.nativeCarrier_smooth
    Uniform.CoefficientCarrierProgram.Construction.UniformCoefficientCarrierProgram 𝒮 schedule (chart.chart.map ≫ f)
      ((Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap chart.chart.map) chart.chart.nativeCarrier
      (fun l => (D l).comap chart.chart.map) localPrefix
  comparisonMap : endpoint ⟶ Y
  comparison : P.EtaleComparison localPrefix chart.chart.map comparisonMap

attribute [instance] ModeledUniformChartProgram.domain ModeledUniformChartProgram.carrierIntegral

end

/-! Pointed retained chart programs give a finite complete modeled atlas on a nonempty compact order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_modeled_uniform_atlas_of_pointed_programs
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : 𝒮.Schedule (n + 1).factorial β}
    {X Y : Scheme} [CompactSpace X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
    {D : β → X.IdealSheafData} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) Y g K}
    (htrace : P.HasIncidenceTrace β D (𝒮.incidenceTrace schedule))
    (ht : letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤)
    (hne : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ≠ ⊤)
    (hcharts : ∀ x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support,
      Nonempty (ModeledUniformChartProgram 𝒮 schedule f J D P x)) :
    Nonempty (UniformCarrierAtlasProgram.Construction.ModeledUniformCarrierAtlasProgram 𝒮 schedule f J D P) := by
  classical
  let ι := {x : X // x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support}
  let C (x : ι) := Classical.choice (hcharts x.val x.property)
  have hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆
      ⋃ x : ι, ((C x).chart.chart.map.opensRange : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (C ⟨x, hx⟩).chart.chart.point, (C ⟨x, hx⟩).chart.chart.point_over⟩
  obtain ⟨s, hs⟩ := (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed.isCompact.elim_finite_subcover
    (fun x : ι => ((C x).chart.chart.map.opensRange : Set X))
    (fun x => (C x).chart.chart.map.opensRange.isOpen) hcover
  have hpoint : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X).Nonempty := by
    by_contra hn
    apply hne
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    apply SetLike.coe_injective
    exact Set.not_nonempty_iff_eq_empty.mp hn
  let : Nonempty s := by
    obtain ⟨x, hx⟩ := hpoint
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact ⟨⟨i, hi⟩⟩
  refine ⟨{
    indices := s
    finite := inferInstance
    nonempty := inferInstance
    point := fun i => i.val.val
    chart := fun i => (C i.val).chart
    domain := fun i => (C i.val).domain
    carrierIntegral := fun i => (C i.val).carrierIntegral
    carrierDimension := fun i => (C i.val).carrierDimension
    cover := ?_
    coefficientNonzero := fun i => (C i.val).coefficientNonzero
    endpoint := fun i => (C i.val).endpoint
    structureMap := fun i => (C i.val).structureMap
    ideal := fun i => (C i.val).ideal
    localPrefix := fun i => (C i.val).localPrefix
    certificate := fun i => (C i.val).certificate
    comparisonMap := fun i => (C i.val).comparisonMap
    comparison := fun i => (C i.val).comparison
    trace := htrace
    terminal := ht }⟩
  intro x hx
  obtain ⟨i, hi, p, hp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact ⟨⟨i, hi⟩, p, hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.UniformAtlasFiniteRefinement.Construction
