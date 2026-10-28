import OAI.AlgebraicGeometry.HodgeConjecture.PresentationBridge
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothDimension

/-! # Products -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Products.CM.SurfaceConstruction

noncomputable section

/-! Native projective products and unconditional use of the geometric
intersection operation on integral projective varieties. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

def projectiveProduct (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    IntersectionTheory.ProjectionFormula.ProperCycleLinearity.ProductPresentation X Y where
  space := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation X Y
  fst := CartesianMonoidalCategory.fst X.toOver Y.toOver
  snd := CartesianMonoidalCategory.snd X.toOver Y.toOver
  isLimit := tensorProductIsBinaryProduct X.toOver Y.toOver

/-- The dimension used by the native analytic realization is the specified
smooth relative dimension. -/
theorem complexDimension_eq_of_smooth (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (d : ℕ)
    [SmoothOfRelativeDimension d X.structureMap] : X.complexDimension = d := by
  let x : X.carrier := Classical.choice inferInstance
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := d) (f := X.structureMap) x
  have hUtop : U = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have hfx : X.structureMap x ∈ U := e hx
      exact (Subsingleton.elim (X.structureMap x) y) ▸ hfx
  subst U
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  let := Betti.AffineDimension.Realization.sectionBaseAlgebra X.structureMap V
  let : Algebra.IsStandardSmoothOfRelativeDimension d
      Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) Γ(X.carrier, V) := hstd
  let : Algebra.IsStandardSmoothOfRelativeDimension X.complexDimension
      Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) Γ(X.carrier, V) :=
    Betti.SmoothDimension.Realization.affineStandardSmooth_dimension X.structureMap V hV
      (show Algebra.IsStandardSmooth Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) Γ(X.carrier, V) from
        Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d)
  exact Foundations.Scheme.StandardSmoothDimension.Algebraic.standardSmooth_dimension_unique
    (R := Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) (S := Γ(X.carrier, V)) X.complexDimension d

theorem product_complexDimension (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety X Y).complexDimension =
      X.complexDimension + Y.complexDimension := by
  let : SmoothOfRelativeDimension X.complexDimension X.structureMap :=
    X.smoothOfRelativeDimension_complexDimension
  let : SmoothOfRelativeDimension Y.complexDimension Y.structureMap :=
    Y.smoothOfRelativeDimension_complexDimension
  let : SmoothOfRelativeDimension (X.complexDimension + Y.complexDimension)
      (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety X Y).structureMap :=
    IntersectionTheory.ProjectionFormula.ProductDimension.relativeDimension (projectiveProduct X.presentation Y.presentation)
      X.complexDimension Y.complexDimension
  exact complexDimension_eq_of_smooth _ _

/-- No auxiliary product or smooth-dimension hypotheses are needed to
multiply algebraic coefficient classes on the actual variety. -/
theorem coefficientCup_algebraic (E : IntermediateField ℚ ℂ)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (u : E ⊗[ℚ] X.rationalCohomology (p + p))
    (v : E ⊗[ℚ] X.rationalCohomology (q + q))
    (hu : u ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X p)
    (hv : v ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X q) :
    Intersections.CM.SurfaceConstruction.extendBilinear E _ _ _ (Intersections.CM.SurfaceConstruction.evenCup X.presentation p q) u v ∈
      Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X (p + q) := by
  let : SmoothOfRelativeDimension X.complexDimension X.structureMap :=
    X.smoothOfRelativeDimension_complexDimension
  exact PresentationBridge.CM.SurfaceConstruction.integral_coefficient_evenCup_algebraic E hThomClass hProjectionFormula X
    (projectiveProduct X.presentation X.presentation) X.complexDimension p q u v hu hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.Products.CM.SurfaceConstruction
