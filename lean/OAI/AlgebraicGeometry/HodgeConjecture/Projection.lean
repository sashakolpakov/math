import OAI.AlgebraicGeometry.HodgeConjecture.Poincare
import OAI.AlgebraicGeometry.HodgeConjecture.CoefficientCups

/-! # Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Projection.CM.SurfaceConstruction

noncomputable section

/-! The projection formula in precisely the degrees used to integrate
the four divisor correspondence along a surface. -/

open _root_.CategoryTheory
open scoped TensorProduct

theorem nativeProjection44 {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : W.toOver ⟶ X.toOver)
    (hdim : W.complexDimension = X.complexDimension + 2)
    (hXdim : 2 ≤ X.complexDimension)
    (a : X.rationalCohomology 4) (b : W.rationalCohomology 4) :
    Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) 4 2 (by omega)
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace W.toOver) 4 4
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 4 f a) b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 4 0 a
        (Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) 2 0 (by omega) b) := by
  let : CompactSpace (Betti.Scheme.schemePointSpace W.toOver) := inferInstanceAs (CompactSpace W.analyticSpace)
  let : CompactSpace (Betti.Scheme.schemePointSpace X.toOver) := inferInstanceAs (CompactSpace X.analyticSpace)
  let : T2Space (Betti.Scheme.schemePointSpace W.toOver) := inferInstanceAs (T2Space W.analyticSpace)
  let : T2Space (Betti.Scheme.schemePointSpace X.toOver) := inferInstanceAs (T2Space X.analyticSpace)
  have h := IntersectionTheory.ProjectionFormula.Chow.Construction.projection_formula (Poincare.CM.SurfaceConstruction.nativePoincareData W) (Poincare.CM.SurfaceConstruction.nativePoincareData X)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) 4 4 0 (2 * X.complexDimension)
      (2 * (X.complexDimension - 2))
    (by omega) (by omega) (by omega) (by omega) a b
  erw [Poincare.CM.SurfaceConstruction.nativePushforward_eq_Functoriality f 4 2 _ (by omega),
    Poincare.CM.SurfaceConstruction.nativePushforward_eq_Functoriality f 2 0 _ (by omega)] at h
  exact h

def coefficientPullback (E : IntermediateField ℚ ℂ)
    {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : W.toOver ⟶ X.toOver) (n : ℕ) :
    (E ⊗[ℚ] X.rationalCohomology n) →ₗ[E] (E ⊗[ℚ] W.rationalCohomology n) :=
  (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f).hom.baseChange E

theorem coefficientProjection44 (E : IntermediateField ℚ ℂ)
    {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : W.toOver ⟶ X.toOver)
    (hdim : W.complexDimension = X.complexDimension + 2)
    (hXdim : 2 ≤ X.complexDimension)
    (a : E ⊗[ℚ] X.rationalCohomology 4) (b : E ⊗[ℚ] W.rationalCohomology 4) :
    (Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) 4 2 (by omega)).baseChange E
        (CoefficientCups.CM.SurfaceConstruction.coefficientCup E W 4 4 (coefficientPullback E f 4 a) b) =
      CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 4 0 a
        ((Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) 2 0 (by omega)).baseChange E b) := by
  induction a using TensorProduct.inductionOn with
  | add a c ha hc => simp [ha, hc]
  | tmul r a =>
    induction b using TensorProduct.inductionOn with
    | add b c hb hc => simp [hb, hc]
    | tmul s b =>
      simp only [CoefficientCups.CM.SurfaceConstruction.coefficientCup, coefficientPullback, LinearMap.baseChange_tmul,
        Intersections.CM.SurfaceConstruction.extendBilinear_tmul]
      exact congrArg (fun z => (r * s) ⊗ₜ[ℚ] z) (nativeProjection44 f hdim hXdim a b)

theorem realizeCoefficient_pullback (E : IntermediateField ℚ ℂ)
    {W X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : W.toOver ⟶ X.toOver) (n : ℕ)
    (a : E ⊗[ℚ] X.rationalCohomology n) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E W n (coefficientPullback E f n a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n a) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul r a =>
    simp only [coefficientPullback, LinearMap.baseChange_tmul, Coefficients.CM.SurfaceConstruction.realizeCoefficient_tmul]
    have h := ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality f n) a
    exact (congrArg (fun z : W.complexCohomology n => (r : ℂ) • z) h).trans
      ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.map_smul (r : ℂ) _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.Projection.CM.SurfaceConstruction
