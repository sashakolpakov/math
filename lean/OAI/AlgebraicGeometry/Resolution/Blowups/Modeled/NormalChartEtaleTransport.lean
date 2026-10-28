import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModeledNormalChart
import OAI.AlgebraicGeometry.Resolution.Blowups.ExplicitLogarithmicDerivationPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealOverlapEquality
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations

/-! # Normal Chart Etale Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Étale algebra transport preserves the full modeled normal-chart data over a new geometric base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart.transportEtale
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    {β : Type} {D : β → X.IdealSheafData} {x : X}
    (C : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D x)
    {V : Scheme} (g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (E : β → V.IdealSheafData) {y : V}
    (T : CommRingCat) [Algebra ℂ T] (φ : C.chart.ring →ₐ[ℂ] T) (hφ : φ.toRingHom.Etale)
    (j : Spec T ⟶ V) [IsOpenImmersion j] (hg : j ≫ g = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure T)
    (hL : L.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (C.chart.ideal.map φ.toRingHom))
    (hE : ∀ i, (E i).comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {φ (C.chart.equations i)}))
    (p : PrimeSpectrum T) (hp : j p = y) : GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart g L n E y := by
  let N := C.model.baseChange φ hφ
  let derivative := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ.toRingHom hφ φ.commutes C.chart.derivative
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
      map := j
      isOpenImmersion := inferInstance
      ground := hg
      ideal := C.chart.ideal.map φ.toRingHom
      ideal_eq := hL
      equations := fun i => φ (C.chart.equations i)
      component := hE
      point := p
      point_over := hp
      normal := φ C.chart.normal
      derivative := derivative
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
  · change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ.toRingHom hφ φ.commutes C.chart.derivative (φ.toRingHom C.chart.normal) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, C.chart.derivative_normal, map_one]
  · rw [← Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map ℂ φ hφ]
    exact Ideal.mem_map_of_mem _ C.chart.normal_mem

end

end OAI.AlgebraicGeometry.Resolution.Blowups
