import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SymbolFrameValues
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientIndependence

/-! # Symbol Local Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.SymbolLocalFrames

noncomputable section

/-! Images of actual algebraic symbols form local holomorphic bases in every degree. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientIndependence

variable {A ι : Type} [CommRing A] [Algebra ℂ A] [Finite ι] [LinearOrder ι] {d : ℕ}

theorem affineChart_symbol_localBasis
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (x : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e)
    (b : Module.Basis ι ℂ (Module.Dual ℂ (Fin d → ℂ))) (a : ι → A)
    (hb : ∀ i, b i = (fderiv ℂ (fun y => e.symm y (a i)) (x : Fin d → ℂ)).toLinearMap) (n : ℕ) :
    ∃ (V : Opens (Fin d → ℂ)) (h : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e), (x : Fin d → ℂ) ∈ V ∧
      ∃ c : Module.Basis (Set.powersetCard ι n) (Holomorphic.FunctionPure.holomorphicFunctions V) (Holomorphic.DeRhamComplex.forms (Fin d → ℂ) V n),
        ∀ s, c s = Holomorphic.HolomorphicPullback.pullback (Opens.inclusion h)
          (contMDiff_inclusion (I := 𝓘(ℂ, Fin d → ℂ)) h) n
            (ChartFormEvaluation.affineChartHolomorphicFormMap e he n (SymbolFrameValues.regularExteriorSymbol a n s)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let family := fun s : Set.powersetCard ι n =>
    ChartFormEvaluation.affineChartHolomorphicFormMap e he n (SymbolFrameValues.regularExteriorSymbol a n s)
  have hid : (fun s => (Holomorphic.CoefficientIndependence.openFormHolomorphicSectionFunctionEquiv (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n (family s)).val x) =
      Pure.CovectorExteriorBasis.Holomorphic.pureCovectorExteriorBasis b n :=
    funext (SymbolFrameValues.affineChart_symbol_coefficients_eq_basis e he x b a hb n)
  have hi : LinearIndependent ℂ
      (fun s => (Holomorphic.CoefficientIndependence.openFormHolomorphicSectionFunctionEquiv (Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) n (family s)).val x) := by
    rw [hid]
    exact (Pure.CovectorExteriorBasis.Holomorphic.pureCovectorExteriorBasis b n).linearIndependent
  have hr := (Holomorphic.CoefficientIndependence.holomorphicCoefficient_linearIndependent_iff n family x).mp hi
  exact Holomorphic.CoefficientIndependence.exists_holomorphicForm_localBasis n (Pure.CovectorExteriorBasis.Holomorphic.pureCovectorExteriorBasis b n) family x hr

omit [Finite ι] [LinearOrder ι] in
theorem affineRegularChart_algebraicImages_localBasis
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin d → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A d) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) (n : ℕ) :
    ∃ (V : Opens (Fin d → ℂ)) (h : V ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e), e x ∈ V ∧
      ∃ I : Type, Finite I ∧
        ∃ c : Module.Basis I (Holomorphic.FunctionPure.holomorphicFunctions V) (Holomorphic.DeRhamComplex.forms (Fin d → ℂ) V n),
          ∀ i, ∃ a : Algebraic.Forms.Form A n, c i = Holomorphic.HolomorphicPullback.pullback (Opens.inclusion h)
            (contMDiff_inclusion (I := 𝓘(ℂ, Fin d → ℂ)) h) n (ChartFormEvaluation.affineChartHolomorphicFormMap e he n a) := by
  classical
  obtain ⟨s, b, a, hb⟩ := RegularDifferentialsSpan.affineRegularChart_exists_differentialBasis e he x hx
  let : Finite s := Module.Finite.finite_basis b
  let : LinearOrder s := linearOrderOfSTO WellOrderingRel
  let q : Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e := ⟨e x, e.map_source hx⟩
  obtain ⟨V, h, hq, c, hc⟩ := affineChart_symbol_localBasis e he q b a hb n
  exact ⟨V, h, hq, Set.powersetCard s n, inferInstance, c,
    fun i => ⟨SymbolFrameValues.regularExteriorSymbol a n i, hc i⟩⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.SymbolLocalFrames
