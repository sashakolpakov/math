import OAI.AlgebraicGeometry.HodgeConjecture.Coefficients
import OAI.AlgebraicGeometry.HodgeConjecture.Intersections
import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralComponent
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImageNaturality

/-! # Presentation Bridge -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.PresentationBridge.CM.SurfaceConstruction

noncomputable section

/-!
Bridge the integral-variety cycle map in SurfaceConstruction and Functoriality to the componentwise
presentation cycle map in ThomClass/ProjectionFormula. The bridge uses the actual component
inclusion isomorphism and proved geometric cycle-class naturality.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem presentation_algebraicClasses_eq (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    X.presentation.geometricAlgebraicClasses p = X.geometricAlgebraicClasses p := by
  ext a
  rw [X.presentation.mem_geometricAlgebraicClasses_iff_components]
  constructor
  · intro h
    have hc := h X.wholeComponent
    rw [X.presentation.componentBettiEquiv_apply] at hc
    have hi : (X.componentOverIso X.wholeComponent).hom =
        X.presentation.componentInclusionOver X.wholeComponent := rfl
    rw [← hi] at hc
    change Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback
      (X.componentOverIso X.wholeComponent).hom (p + p) a ∈
        (X.presentation.componentVariety X.wholeComponent).geometricAlgebraicClasses p at hc
    exact (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff
      (X.componentOverIso X.wholeComponent) p a).mp hc
  · intro h C
    rw [X.presentation.componentBettiEquiv_apply]
    have hi : (X.componentOverIso C).hom = X.presentation.componentInclusionOver C := rfl
    rw [← hi]
    change Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback
      (X.componentOverIso C).hom (p + p) a ∈
        (X.presentation.componentVariety C).geometricAlgebraicClasses p
    exact (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff
      (X.componentOverIso C) p a).mpr h

/-- The image of a base-changed rational map is the base change of its image. -/
theorem range_baseChange (E U V : Type*) [Field E] [Algebra ℚ E]
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (f : U →ₗ[ℚ] V) :
    LinearMap.range (f.baseChange E) = (LinearMap.range f).baseChange E := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | tmul a u =>
      exact Submodule.tmul_mem_baseChange_of_mem a (show f u ∈ LinearMap.range f from ⟨u, rfl⟩)
  · rintro x ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | tmul a u =>
      obtain ⟨v, hv⟩ := u.property
      refine ⟨a ⊗ₜ[ℚ] v, ?_⟩
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hv]
      rfl

/-- The two native cycle models give exactly the same coefficient classes. -/
theorem presentation_coefficientAlgebraicClasses_eq
    (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Intersections.CM.SurfaceConstruction.presentationCoefficientAlgebraicClasses E X.presentation p = Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X p := by
  unfold Intersections.CM.SurfaceConstruction.presentationCoefficientAlgebraicClasses Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses
  rw [range_baseChange, range_baseChange]
  exact congrArg (fun P : Submodule ℚ (X.rationalCohomology (p + p)) => P.baseChange E)
    (presentation_algebraicClasses_eq X p)

/-- ThomClass/ProjectionFormula cup algebraicity now applies to exactly the integral cycle
image used in the SurfaceConstruction target and in its proper-pushforward helpers. -/
theorem integral_coefficient_evenCup_algebraic (E : IntermediateField ℚ ℂ)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (P : IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X.presentation X.presentation)
    (d : ℕ) [SmoothOfRelativeDimension d X.structureMap] (p q : ℕ)
    (u : E ⊗[ℚ] X.rationalCohomology (p + p))
    (v : E ⊗[ℚ] X.rationalCohomology (q + q))
    (hu : u ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X p)
    (hv : v ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X q) :
    Intersections.CM.SurfaceConstruction.extendBilinear E _ _ _ (Intersections.CM.SurfaceConstruction.evenCup X.presentation p q) u v ∈
      Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X (p + q) := by
  rw [← presentation_coefficientAlgebraicClasses_eq] at hu hv ⊢
  exact Intersections.CM.SurfaceConstruction.coefficient_evenCup_algebraic E hThomClass hProjectionFormula X.presentation P d p q u v hu hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.PresentationBridge.CM.SurfaceConstruction
