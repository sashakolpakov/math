import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation

/-! # Betti Conjugation Involution -/

namespace OAI.RepresentationTheory.Theta.Geometric.BettiConjugationInvolution

noncomputable section

/-! Actual singular-cochain conjugation is involutive, and is natural
for the algebraic pullbacks used by the original Albanese H1. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Simplicial
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction

theorem conjugateCochain_involutive (S : SSet.{0}) (n : ℕ) :
    Function.Involutive (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialCochain S n) := by
  intro c
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).toLinearEquiv.injective
  funext z
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).hom
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialCochain S n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialCochain S n c)) z =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso S (ModuleCat.of ℂ ℂ) n).hom c z
  exact (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialCochain_function S n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialCochain S n c) z).trans
    ((congrArg star (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialCochain_function S n c z)).trans (star_star _))

theorem conjugateH1_involutive (S : SSet.{0}) :
    Function.Involutive (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialH1 S) := by
  intro x
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains S (ModuleCat.of ℂ ℂ)) 1 x
  simp only [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialH1, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.semilinearH1Map_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 1)
  apply Subtype.ext
  exact conjugateCochain_involutive S 1 c.val

theorem conjugateBetti_involutive (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Function.Involutive (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X) :=
  conjugateH1_involutive _

theorem conjugateBetti_pullback (X Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ Y.toOver)
    (x : Y.complexCohomology 1) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f x) =
      AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 Y x) :=
  AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CochainConjugation.CM.Construction.conjugateSimplicialH1_pullback (TopCat.toSSet.map (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)) x

end

end OAI.RepresentationTheory.Theta.Geometric.BettiConjugationInvolution
