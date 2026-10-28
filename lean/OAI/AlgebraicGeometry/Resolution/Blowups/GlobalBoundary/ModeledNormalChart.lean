import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientDifferentialLocus
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientCoordinateChart
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.AdjoinCoordinate
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.LogarithmicLe
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport

/-! # Modeled Normal Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModeledNormalChart.Construction

noncomputable section

section

/-! A full logarithmic bound supplies actual transverse normal charts along the global order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure GlobalBoundaryNormalChart {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (J : X.IdealSheafData) (n : ℕ) {β : Type} (D : β → X.IdealSheafData) (x : X) where
  ring : CommRingCat
  algebra : Algebra ℂ ring
  map : Spec ring ⟶ X
  isOpenImmersion : IsOpenImmersion map
  ground : map ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure ring
  ideal : Ideal ring
  ideal_eq : J.comap map = Affine.QuotientKernel.Construction.affineQuotientKernel ideal
  equations : β → ring
  component : ∀ j, (D j).comap map = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {equations j})
  point : PrimeSpectrum ring
  point_over : map point = x
  normal : ring
  derivative : Derivation ℂ ring ring
  derivative_normal : derivative normal = 1
  normal_mem : normal ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ ideal n
  smooth : Algebra.Smooth ℂ ring
  coefficientBoundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (ring ⧸ Ideal.span {normal}))
    (fun j => Ideal.Quotient.mk (Ideal.span {normal}) (equations j))
  fullBoundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ ring
    (fun j : Option β => match j with | none => normal | some l => equations l)

attribute [instance] GlobalBoundaryNormalChart.algebra GlobalBoundaryNormalChart.isOpenImmersion
  GlobalBoundaryNormalChart.smooth

theorem exists_global_boundary_normal_chart
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {β : Type} [Fintype β]
    {D : β → X.IdealSheafData} (B : ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (J : X.IdealSheafData) (n : ℕ) (hbound : B.logarithmicIdeal J (n + 1) = ⊤)
    (x : X) (hx : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    Nonempty (GlobalBoundaryNormalChart f J n D x) := by
  have hxcover : x ∈ ⨆ i, (B.map i).opensRange := by rw [B.cover]; trivial
  obtain ⟨i, p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  let : Algebra.Smooth ℂ (B.rings i) := (B.model i).smooth
  have hlog : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ (B.equations i) (B.affineIdeal J i) (n + 1) = ⊤ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [DifferentialUnitGluing.Construction.affineQuotientKernel_top, ← B.logarithmicIdeal_restrict J (n + 1) i,
      hbound, Scheme.IdealSheafData.comap_top]
  have hdiff : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (B.affineIdeal J i) n ≤ p.asIdeal := by
    have hs := congrArg (fun K : (Spec (B.rings i)).IdealSheafData => (K.support : Set (Spec (B.rings i))))
      (B.ordinaryIdeal_restrict J n i)
    rw [Scheme.IdealSheafData.support_comap, Coefficient.ChartSupport.Construction.affineQuotientKernel_support] at hs
    change p ∈ PrimeSpectrum.zeroLocus (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (B.affineIdeal J i) n)
    rw [← hs]
    change B.map i p ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support
    rw [hp]
    exact hx
  obtain ⟨C⟩ := Boundary.CoefficientDifferentialLocus.Construction.exists_boundary_coefficient_chart_of_differential_locus (B.rings i)
    (B.equations i) (B.model i).hasEtaleBoundaryCharts (B.affineIdeal J i) n hlog p hdiff
  obtain ⟨G⟩ := Boundary.CoefficientCoordinateChart.Construction.exists_boundary_coefficient_coordinate_refinement C
  let A := G.chart
  let : Algebra ℂ A.carrier := A.algebra
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom A.map.toRingHom)) := A.isOpenImmersion
  let j := Spec.map (CommRingCat.ofHom A.map.toRingHom) ≫ B.map i
  refine ⟨{
    ring := A.carrier
    algebra := A.algebra
    map := j
    isOpenImmersion := inferInstance
    ground := ?_
    ideal := (B.affineIdeal J i).map A.map.toRingHom
    ideal_eq := ?_
    equations := fun l => A.map (B.equations i l)
    component := ?_
    point := A.point
    point_over := by
      change B.map i (PrimeSpectrum.comap A.map.toRingHom A.point) = x
      exact (congrArg (B.map i) A.point_over).trans hp
    normal := A.normal
    derivative := A.derivative
    derivative_normal := A.derivative_normal
    normal_mem := A.normal_mem
    smooth := A.ambientModel.smooth
    coefficientBoundary := A.coefficientModel.hasEtaleBoundaryCharts
    fullBoundary := (A.ambientModel.adjoinEquation A.normal G.normalIndex
      G.normal_unused G.normal_eq).hasEtaleBoundaryCharts }⟩
  · change (Spec.map (CommRingCat.ofHom A.map.toRingHom) ≫ B.map i) ≫ f = _
    rw [Category.assoc, B.ground i]
    change Spec.map (CommRingCat.ofHom A.map.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (B.rings i))) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact A.map.commutes c
  · rw [Scheme.IdealSheafData.comap_comp, B.affineIdeal_eq, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  · intro l
    rw [Scheme.IdealSheafData.comap_comp, B.component, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      Ideal.map_span, Set.image_singleton]

end

/-! Pointed normal charts retain their actual boundary coordinate model and logarithmic normal derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure GlobalBoundaryModeledNormalChart {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (J : X.IdealSheafData) (n : ℕ) {β : Type} (D : β → X.IdealSheafData) (x : X) where
  chart : GlobalBoundaryNormalChart f J n D x
  model : Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ chart.ring β chart.equations
  normalIndex : model.indices
  normal_eq : model.map (MvPolynomial.X normalIndex) = chart.normal
  normal_unused : ∀ j, model.coordinate j ≠ some normalIndex
  derivative_tangent : chart.derivative ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations ℂ chart.equations

theorem exists_global_boundary_modeled_normal_chart
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {β : Type} [Fintype β]
    {D : β → X.IdealSheafData} (B : ModelAtlas.Construction.GlobalBoundaryModelAtlas f D)
    (J : X.IdealSheafData) (n : ℕ) (hbound : B.logarithmicIdeal J (n + 1) = ⊤)
    (x : X) (hx : x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) :
    Nonempty (GlobalBoundaryModeledNormalChart f J n D x) := by
  have hxcover : x ∈ ⨆ i, (B.map i).opensRange := by rw [B.cover]; trivial
  obtain ⟨i, p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  let : Algebra.Smooth ℂ (B.rings i) := (B.model i).smooth
  have hlog : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal ℂ (B.equations i) (B.affineIdeal J i) (n + 1) = ⊤ := by
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
    rw [DifferentialUnitGluing.Construction.affineQuotientKernel_top, ← B.logarithmicIdeal_restrict J (n + 1) i,
      hbound, Scheme.IdealSheafData.comap_top]
  have hdiff : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (B.affineIdeal J i) n ≤ p.asIdeal := by
    have hs := congrArg (fun K : (Spec (B.rings i)).IdealSheafData => (K.support : Set (Spec (B.rings i))))
      (B.ordinaryIdeal_restrict J n i)
    rw [Scheme.IdealSheafData.support_comap, Coefficient.ChartSupport.Construction.affineQuotientKernel_support] at hs
    change p ∈ PrimeSpectrum.zeroLocus (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (B.affineIdeal J i) n)
    rw [← hs]
    change B.map i p ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support
    rw [hp]
    exact hx
  obtain ⟨C⟩ := Boundary.CoefficientDifferentialLocus.Construction.exists_boundary_coefficient_chart_of_differential_locus (B.rings i)
    (B.equations i) (B.model i).hasEtaleBoundaryCharts (B.affineIdeal J i) n hlog p hdiff
  obtain ⟨G⟩ := Boundary.CoefficientCoordinateChart.Construction.exists_boundary_coefficient_coordinate_refinement C
  let A := G.chart
  let : Algebra ℂ A.carrier := A.algebra
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom A.map.toRingHom)) := A.isOpenImmersion
  let j := Spec.map (CommRingCat.ofHom A.map.toRingHom) ≫ B.map i
  refine ⟨{
    chart := {
      ring := A.carrier
      algebra := A.algebra
      map := j
      isOpenImmersion := inferInstance
      ground := ?_
      ideal := (B.affineIdeal J i).map A.map.toRingHom
      ideal_eq := ?_
      equations := fun l => A.map (B.equations i l)
      component := ?_
      point := A.point
      point_over := by
        change B.map i (PrimeSpectrum.comap A.map.toRingHom A.point) = x
        exact (congrArg (B.map i) A.point_over).trans hp
      normal := A.normal
      derivative := A.derivative
      derivative_normal := A.derivative_normal
      normal_mem := A.normal_mem
      smooth := A.ambientModel.smooth
      coefficientBoundary := A.coefficientModel.hasEtaleBoundaryCharts
      fullBoundary := (A.ambientModel.adjoinEquation A.normal G.normalIndex
        G.normal_unused G.normal_eq).hasEtaleBoundaryCharts }
    model := A.ambientModel
    normalIndex := G.normalIndex
    normal_eq := G.normal_eq
    normal_unused := G.normal_unused
    derivative_tangent := A.derivative_tangent }⟩
  · change (Spec.map (CommRingCat.ofHom A.map.toRingHom) ≫ B.map i) ≫ f = _
    rw [Category.assoc, B.ground i]
    change Spec.map (CommRingCat.ofHom A.map.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (B.rings i))) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact A.map.commutes c
  · rw [Scheme.IdealSheafData.comap_comp, B.affineIdeal_eq, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  · intro l
    rw [Scheme.IdealSheafData.comap_comp, B.component, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      Ideal.map_span, Set.image_singleton]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModeledNormalChart.Construction
