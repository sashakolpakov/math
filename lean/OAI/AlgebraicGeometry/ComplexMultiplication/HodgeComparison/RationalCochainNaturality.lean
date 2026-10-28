import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicTopology.Cohomology.Singular.Augmentation

/-! # Rational Cochain Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCochainNaturality.CM.Construction

noncomputable section

/-! Actual coefficient inclusion commutes with pullback of cochains and
casts the values of zero-cochains at points. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.Augmentation
open scoped Simplicial

theorem rationalToComplexCochain_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y).X n) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f).f n ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain Y).f n c) =
      (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f n ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f n c) := by
  let cY : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y).X n :=
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain Y).f n c
  let r : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n :=
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f).f n c
  let cX : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X).X n :=
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f n r
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) f).f n cY = cX
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) n).toLinearEquiv.injective
  funext s
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) n).hom _ s =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) n).hom cX s
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  have hY : AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) (ModuleCat.of ℂ ℂ)
      ((TopCat.toSSet.map f).app _ s) cY =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.map f).app _ s) c : ℂ) :=
    PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation Y n c _
  have hX : AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s cX =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) s r : ℂ) :=
    PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation X n r s
  exact ((AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of ℂ ℂ) (TopCat.toSSet.map f) cY s).trans hY).trans
    ((congrArg (fun q : ℚ => (q : ℂ))
      (AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of ℚ ℚ) (TopCat.toSSet.map f) c s).symm).trans hX.symm)

theorem rationalToComplexCochain_point (X : TopCat.{0})
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X 0) (x : X) :
    (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℂ ℂ) X).hom
      ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f 0 c) x =
        ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) X).hom c x : ℂ) := by
  let cX : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X).X 0 :=
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f 0 c
  change (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℂ ℂ) X).hom cX x = _
  rw [AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply, AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply,
    AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply, AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  exact PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation X 0 c (TopCat.toSSetObj₀Equiv.symm x)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCochainNaturality.CM.Construction
