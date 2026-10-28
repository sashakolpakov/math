import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DeRhamTopCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.RationalProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve

/-! # Positive Top Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PositiveTopCup

noncomputable section

/-! The genuine nonzero projective top cup can be written using only
positive-degree products; no degree-zero comparison is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechBettiEquivalence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev cup (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (x : DeRhamTopCup.H V p) (y : DeRhamTopCup.H V q) :=
  IntegralDeRham.CechProduct.cohomologyCup ℂ V.toOver
    (NonemptyCechNerve.nerve (CechBettiEquivalence.cover V)) p q x y

abbrev bettiCup (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (x : A.variety.complexCohomology p) (y : A.variety.complexCohomology q) :=
  AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) p q x y

theorem betti_product (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin (n+1) → A.variety.complexCohomology 1) :
    AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A (n+1) v =
      GradedPositiveProduct.product (bettiCup A) n v := by
  induction n with
  | zero =>
      change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) 0 1
        (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver)) (v 0) = v 0
      simpa only [AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast, LinearMap.id_apply] using
        (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit_cup (TopCat.toSSet.obj (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver)) (v 0))
  | succ n ih =>
      change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) (n+1) 1
        (AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A (n+1) (Fin.init v)) (v (Fin.last (n+1))) = _
      rw [ih]
      rfl

theorem comparison_cup (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (x : DeRhamTopCup.H A.variety p)
    (y : DeRhamTopCup.H A.variety q) :
    CechBettiEquivalence.algebraicEquiv A.variety (p+q) (cup A.variety p q x y) =
      bettiCup A p q (CechBettiEquivalence.algebraicEquiv A.variety p x) (CechBettiEquivalence.algebraicEquiv A.variety q y) := by
  change CechBettiEquivalence.algebraicEquiv A.variety (p+q)
    (IntegralDeRham.CechProduct.cohomologyCup ℂ A.toOver
      (NonemptyCechNerve.nerve (CechBettiEquivalence.cover A.variety)) p q x y) = _
  rw [IntegralDeRham.RationalProduct.Cech.cohomologyCup_eq_rational]
  exact CechBettiEquivalence.algebraicEquiv_cup A.variety p q x y

theorem exists_nonzero (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (hn : n+1 = 2*A.variety.complexDimension) :
    ∃ v : Fin (n+1) → DeRhamTopCup.H A.variety 1,
      GradedPositiveProduct.product (cup A.variety) n v ≠ 0 := by
  have hex : ∃ v : Fin (n+1) → A.variety.complexCohomology 1,
      AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A (n+1) v ≠ 0 := by
    rw [hn]
    exact BettiTopCup.exists_nonzero A
  obtain ⟨v, hv⟩ := hex
  let w := fun i => (CechBettiEquivalence.algebraicEquiv A.variety 1).symm (v i)
  refine ⟨w, ?_⟩
  intro hz
  have hc := GradedPositiveProduct.natural (cup A.variety) (bettiCup A)
    (fun q => CechBettiEquivalence.algebraicEquiv A.variety q) (comparison_cup A) n w
  apply hv
  rw [betti_product]
  simpa only [w, LinearEquiv.apply_symm_apply, hz, map_zero] using hc.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PositiveTopCup
