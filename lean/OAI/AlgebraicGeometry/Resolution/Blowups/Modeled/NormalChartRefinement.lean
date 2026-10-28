import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModeledNormalChart
import OAI.AlgebraicGeometry.Resolution.Blowups.ExplicitLogarithmicDerivationPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealOverlapEquality
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations

/-! # Normal Chart Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual affine open refinement preserves all normal-chart data, including its boundary coordinate model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart.refine
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x)
    (T : CommRingCat) [Algebra ℂ T] (φ : C.chart.ring →ₐ[ℂ] T)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    (p : PrimeSpectrum T) (hp : PrimeSpectrum.comap φ.toRingHom p = C.chart.point) :
    GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x := by
  have hφ : φ.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom φ.toRingHom)).mp inferInstance
  let N := C.model.baseChange φ hφ
  let E := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ.toRingHom hφ φ.commutes C.chart.derivative
  have hnormal : N.map (MvPolynomial.X C.normalIndex) = φ C.chart.normal := by
    change φ.toRingHom (C.model.map (MvPolynomial.X C.normalIndex)) = φ C.chart.normal
    rw [C.normal_eq]
    rfl
  have hcoeff : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ (T ⧸ Ideal.span {φ C.chart.normal}) β
      (fun i => Ideal.Quotient.mk (Ideal.span {φ C.chart.normal}) (φ (C.chart.equations i))) := by
    have he := congrArg (fun z : T => Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ (T ⧸ Ideal.span {z}) β
      (fun i => Ideal.Quotient.mk (Ideal.span {z}) (φ (C.chart.equations i)))) hnormal
    exact he ▸ N.transverseCoordinateFiber C.normalIndex C.normal_unused
  refine {
    chart := {
      ring := T
      algebra := inferInstance
      map := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ C.chart.map
      isOpenImmersion := inferInstance
      ground := ?_
      ideal := C.chart.ideal.map φ.toRingHom
      ideal_eq := ?_
      equations := fun i => φ (C.chart.equations i)
      component := ?_
      point := p
      point_over := ?_
      normal := φ C.chart.normal
      derivative := E
      derivative_normal := ?_
      normal_mem := ?_
      smooth := N.smooth
      coefficientBoundary := hcoeff.hasEtaleBoundaryCharts
      fullBoundary := (N.adjoinEquation (φ C.chart.normal) C.normalIndex C.normal_unused hnormal).hasEtaleBoundaryCharts }
    model := N
    normalIndex := C.normalIndex
    normal_eq := hnormal
    normal_unused := C.normal_unused
    derivative_tangent := ExplicitLogarithmicDerivationPullback.Construction.extendEtaleRingDerivationHom_relative_logarithmic φ hφ C.chart.equations
      C.chart.derivative C.derivative_tangent }
  · rw [Category.assoc, C.chart.ground]
    exact Affine.IdealOverlapEquality.Construction.complexSpecStructure_specMap_algHom C.chart.ring T φ
  · rw [Scheme.IdealSheafData.comap_comp, C.chart.ideal_eq, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  · intro i
    rw [Scheme.IdealSheafData.comap_comp, C.chart.component, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
      Ideal.map_span, Set.image_singleton]
  · change C.chart.map (PrimeSpectrum.comap φ.toRingHom p) = x
    rw [hp]
    exact C.chart.point_over
  · change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ.toRingHom hφ φ.commutes C.chart.derivative (φ.toRingHom C.chart.normal) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, C.chart.derivative_normal, map_one]
  · rw [← Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map ℂ φ hφ]
    exact Ideal.mem_map_of_mem _ C.chart.normal_mem

end

end OAI.AlgebraicGeometry.Resolution.Blowups
