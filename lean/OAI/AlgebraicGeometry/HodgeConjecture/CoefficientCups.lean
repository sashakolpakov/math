import OAI.AlgebraicGeometry.HodgeConjecture.Pairs
import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionQ
import OAI.AlgebraicGeometry.HodgeConjecture.Products
import OAI.AlgebraicGeometry.HodgeConjecture.CupRegrouping

/-! # Coefficient Cups -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CoefficientCups.CM.SurfaceConstruction

noncomputable section

/-! Scalar extension of the actual cup product in all degrees, and the
algebraic product of four actual opposite-embedding divisor classes. -/

open _root_.CategoryTheory
open scoped TensorProduct

def coefficientCup (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p q : ℕ) : (E ⊗[ℚ] X.rationalCohomology p) →ₗ[E]
      (E ⊗[ℚ] X.rationalCohomology q) →ₗ[E]
        (E ⊗[ℚ] X.rationalCohomology (p + q)) :=
  Intersections.CM.SurfaceConstruction.extendBilinear E _ _ _
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) p q)

theorem realizeCoefficient_cup (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (u : E ⊗[ℚ] X.rationalCohomology p) (v : E ⊗[ℚ] X.rationalCohomology q) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X (p + q) (coefficientCup E X p q u v) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) p q
        (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X p u) (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X q v) := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp [hu, hw]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp [hv, hw]
    | tmul b y =>
      simp only [coefficientCup, Intersections.CM.SurfaceConstruction.extendBilinear_tmul, Coefficients.CM.SurfaceConstruction.realizeCoefficient_tmul,
        IntermediateField.coe_mul]
      change ((a : ℂ) * (b : ℂ)) •
        AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) (p + q)
          (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) p q x y) =
        AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) p q
          ((a : ℂ) • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) p x)
          ((b : ℂ) • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) q y)
      erw [map_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul, mul_comm (b : ℂ) (a : ℂ)]
      exact congrArg (fun z => ((a : ℂ) * (b : ℂ)) • z)
        (ComplexMultiplication.HodgeComparison.RationalCup.CM.Construction.rationalToComplexCohomology_cup (Betti.Scheme.schemePointSpace X.toOver) p q x y)

theorem coefficientCup_conjugate (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) (σ : Gal(E/ℚ))
    (u : E ⊗[ℚ] X.rationalCohomology p) (v : E ⊗[ℚ] X.rationalCohomology q) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology (p + q)) σ (coefficientCup E X p q u v) =
      coefficientCup E X p q
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology p) σ u)
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology q) σ v) := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp [hu, hw]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp [hv, hw]
    | tmul b y => simp [coefficientCup, Intersections.CM.SurfaceConstruction.extendBilinear_tmul]

def coefficientFourCup (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Fin 4 → E ⊗[ℚ] X.rationalCohomology 1) : E ⊗[ℚ] X.rationalCohomology 4 :=
  coefficientCup E X 2 2 (coefficientCup E X 1 1 (u 0) (u 1))
    (coefficientCup E X 1 1 (u 2) (u 3))

theorem realizeCoefficient_fourCup (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Fin 4 → E ⊗[ℚ] X.rationalCohomology 1) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 4 (coefficientFourCup E X u) =
      SurfaceConstructionQ.CM.fourCup X (fun i => Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 1 (u i)) := by
  unfold coefficientFourCup SurfaceConstructionQ.CM.fourCup
  erw [realizeCoefficient_cup E X 2 2, realizeCoefficient_cup E X 1 1,
    realizeCoefficient_cup E X 1 1]

theorem coefficientFourCup_conjugate (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Fin 4 → E ⊗[ℚ] X.rationalCohomology 1)
    (σ : Gal(E/ℚ)) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 4) σ (coefficientFourCup E X u) =
      coefficientFourCup E X (fun i => ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 1) σ (u i)) := by
  unfold coefficientFourCup
  erw [coefficientCup_conjugate E X 2 2, coefficientCup_conjugate E X 1 1,
    coefficientCup_conjugate E X 1 1]

def fourDivisorCup (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Fin 4 → E ⊗[ℚ] X.rationalCohomology 2) : E ⊗[ℚ] X.rationalCohomology 8 :=
  coefficientCup E X 4 4 (coefficientCup E X 2 2 (u 0) (u 1))
    (coefficientCup E X 2 2 (u 2) (u 3))

private theorem evenCup11 (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Intersections.CM.SurfaceConstruction.evenCup X 1 1 = AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 2 2 := rfl

private theorem evenCup22 (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Intersections.CM.SurfaceConstruction.evenCup X 2 2 = AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 4 4 := rfl

theorem fourDivisorCup_algebraic (E : IntermediateField ℚ ℂ)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Fin 4 → E ⊗[ℚ] X.rationalCohomology 2)
    (hu : ∀ i, u i ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 1) :
    fourDivisorCup E X u ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 4 := by
  have h01 := Products.CM.SurfaceConstruction.coefficientCup_algebraic E hThomClass hProjectionFormula X 1 1 (u 0) (u 1) (hu 0) (hu 1)
  have h23 := Products.CM.SurfaceConstruction.coefficientCup_algebraic E hThomClass hProjectionFormula X 1 1 (u 2) (u 3) (hu 2) (hu 3)
  rw [evenCup11] at h01 h23
  change coefficientCup E X 2 2 (u 0) (u 1) ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 at h01
  change coefficientCup E X 2 2 (u 2) (u 3) ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 at h23
  have h := Products.CM.SurfaceConstruction.coefficientCup_algebraic E hThomClass hProjectionFormula X 2 2
    (coefficientCup E X 2 2 (u 0) (u 1)) (coefficientCup E X 2 2 (u 2) (u 3)) h01 h23
  rw [evenCup22] at h
  exact h

/-- The realization of four native divisor pairs is the exterior cup of
the two fourfold classes, with the sign proved on singular cohomology. -/
theorem fourDivisorCup_realize_regroup (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Fin 4 → E ⊗[ℚ] X.rationalCohomology 2)
    (a b : Fin 4 → X.complexCohomology 1)
    (hu : ∀ i, Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 2 (u i) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1 (a i) (b i)) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 8 (fourDivisorCup E X u) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 4 4
        (SurfaceConstructionQ.CM.fourCup X a) (SurfaceConstructionQ.CM.fourCup X b) := by
  unfold fourDivisorCup
  erw [realizeCoefficient_cup E X 4 4, realizeCoefficient_cup E X 2 2,
    realizeCoefficient_cup E X 2 2]
  simp only [hu, SurfaceConstructionQ.CM.fourCup]
  exact CupRegrouping.CM.SurfaceConstruction.four_pair_cup_regroup (Betti.Scheme.schemePointSpace X.toOver) a b

end

end OAI.AlgebraicGeometry.HodgeConjecture.CoefficientCups.CM.SurfaceConstruction
