import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Cup
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ScalarExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCup
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Complex Operations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations.CM.Construction

noncomputable section

/-! The native cycle operations preserve the actual complex algebraic
class spaces. All maps are scalar extensions of the rational operations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem cohomologyCast_eq_cast {R : Type} [CommRing R]
    (X : TopCat.{0}) {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n) :
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) h a =
      cast (congrArg (fun d => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X d : Type)) h) a := by
  subst m
  rfl

def evenCup (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (p + p) →ₗ[R]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X (q + q) →ₗ[R]
        AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X ((p + q) + (p + q)) :=
  (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X (p + p) (q + q)).compr₂
    (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (add_add_add_comm p p q q))

theorem rationalToComplex_cast (X : TopCat.{0}) {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X m
      (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) h a) =
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) h
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n a) := by
  subst m
  rfl

theorem rationalToComplex_evenCup (X : TopCat.{0}) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (p + p))
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (q + q)) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X ((p + q) + (p + q)) (evenCup ℚ X p q a b) =
      evenCup ℂ X p q (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X (p + p) a)
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X (q + q) b) := by
  change AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X _ (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast _ _ _ _) = _
  rw [rationalToComplex_cast, ComplexMultiplication.HodgeComparison.RationalCup.CM.Construction.rationalToComplexCohomology_cup]
  rfl

theorem complex_cup_algebraic (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (a : X.complexCohomology (p + p)) (b : X.complexCohomology (q + q))
    (ha : a ∈ X.complexGeometricAlgebraicClasses p)
    (hb : b ∈ X.complexGeometricAlgebraicClasses q) :
    evenCup ℂ (Betti.Scheme.schemePointSpace X.toOver) p q a b ∈
      X.complexGeometricAlgebraicClasses (p + q) := by
  apply ScalarExtension.CM.Construction.bilinear_preserves_complex_image
    (X.geometricAlgebraicClasses p) (X.geometricAlgebraicClasses q)
    (X.geometricAlgebraicClasses (p + q))
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (p + p))
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (q + q))
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) ((p + q) + (p + q)))
    (evenCup ℚ (Betti.Scheme.schemePointSpace X.toOver) p q) _ ?_ ?_ a b ha hb
  · intro x hx y hy
    change AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast _ _ _ _ ∈ _
    rw [cohomologyCast_eq_cast]
    exact Cup.CM.Construction.rational_cup_algebraic h_LineBundleCycles h_ThomClass X p q x y hx hy
  · intro x y
    simp only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
    exact (rationalToComplex_evenCup (Betti.Scheme.schemePointSpace X.toOver) p q x y).symm

theorem complex_pullback_algebraic (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput)
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver)
    (p : ℕ) (a : Y.complexCohomology (p + p))
    (ha : a ∈ Y.complexGeometricAlgebraicClasses p) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + p) f a ∈
      X.complexGeometricAlgebraicClasses p := by
  apply ScalarExtension.CM.Construction.linear_preserves_complex_image (Y.geometricAlgebraicClasses p)
    (X.geometricAlgebraicClasses p)
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) (p + p))
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (p + p))
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f).hom _ ?_ ?_ a ha
  · intro x hx
    rw [← IntegralPresentation.CM.Construction.integral_presentation_geometricClasses Y p] at hx
    rw [← IntegralPresentation.CM.Construction.integral_presentation_geometricClasses X p]
    exact CycleOperations.CM.Construction.rational_pullback_algebraic h_LineBundleCycles X.presentation Y.presentation f p x hx
  · intro x
    simp only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
    exact (ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality f (p + p)) x).symm

def projectiveComplexification (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology n) ≃ₗ[ℂ] X.complexCohomology n := by
  let : Module.Finite ℚ (X.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X n
  exact ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace X.toOver) n

def complexPushforward {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ) (hdeg : p + Y.complexDimension = q + X.complexDimension) :
    X.complexCohomology (p + p) →ₗ[ℂ] Y.complexCohomology (q + q) :=
  (projectiveComplexification Y (q + q)).toLinearMap.comp
    (((Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg).baseChange ℂ).comp
      (projectiveComplexification X (p + p)).symm.toLinearMap)

theorem complexPushforward_comparison {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ) (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (a : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology (p + p))) :
    complexPushforward f hf p q hdeg
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (p + p) a) =
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) (q + q)
      ((Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg).baseChange ℂ a) := by
  change projectiveComplexification Y (q + q)
    ((Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg).baseChange ℂ
      ((projectiveComplexification X (p + p)).symm
        (projectiveComplexification X (p + p) a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem complex_pushforward_algebraic (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput)
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    (p q : ℕ) (hdeg : p + Y.complexDimension = q + X.complexDimension)
    (a : X.complexCohomology (p + p))
    (ha : a ∈ X.complexGeometricAlgebraicClasses p) :
    complexPushforward f hf p q hdeg a ∈ Y.complexGeometricAlgebraicClasses q := by
  apply ScalarExtension.CM.Construction.linear_preserves_complex_image (X.geometricAlgebraicClasses p)
    (Y.geometricAlgebraicClasses q)
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (p + p))
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) (q + q))
    (Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg) _
    (CycleOperations.CM.Construction.rational_pushforward_algebraic h_Functoriality f hf p q hdeg) ?_ a ha
  intro x
  rw [complexPushforward_comparison, LinearMap.baseChange_tmul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations.CM.Construction
