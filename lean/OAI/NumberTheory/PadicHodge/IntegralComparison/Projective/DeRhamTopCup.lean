import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechBettiEquivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.BettiTopCup

/-! # De Rham Top Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DeRhamTopCup

noncomputable section

/-! A nonzero iterated product of degree-one classes in the actual
algebraic Čech–de Rham cohomology of an abelian variety. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechBettiEquivalence

abbrev H (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :=
  (RationalDeRham.TotalCup.Cech.total ℂ V.toOver
    (Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (CechBettiEquivalence.cover V))).homology n

def cupFrom (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : H V 0) :
    (n : ℕ) → (Fin n → H V 1) → H V n
  | 0, _ => u
  | n + 1, v => RationalDeRham.CohomologyCup.Cech.cohomologyCup ℂ V.toOver
      (Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (CechBettiEquivalence.cover V)) n 1
      (cupFrom V u n (Fin.init v)) (v (Fin.last n))

def bettiCupFrom (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : V.complexCohomology 0) :
    (n : ℕ) → (Fin n → V.complexCohomology 1) → V.complexCohomology n
  | 0, _ => u
  | n + 1, v => AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) n 1
      (bettiCupFrom V u n (Fin.init v)) (v (Fin.last n))

theorem comparison_cupFrom (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : H V 0)
    (n : ℕ) (v : Fin n → H V 1) :
    CechBettiEquivalence.algebraicEquiv V n (DeRhamTopCup.cupFrom V u n v) =
      DeRhamTopCup.bettiCupFrom V (CechBettiEquivalence.algebraicEquiv V 0 u) n (fun i => CechBettiEquivalence.algebraicEquiv V 1 (v i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change CechBettiEquivalence.algebraicEquiv V (n + 1)
        (RationalDeRham.CohomologyCup.Cech.cohomologyCup ℂ V.toOver
          (Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (CechBettiEquivalence.cover V)) n 1
          (DeRhamTopCup.cupFrom V u n (Fin.init v)) (v (Fin.last n))) = _
      rw [CechBettiEquivalence.algebraicEquiv_cup, ih]
      rfl

theorem bettiCupFrom_unit (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin n → A.variety.complexCohomology 1) :
    DeRhamTopCup.bettiCupFrom A.variety (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver)) n v =
      AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) n 1
        (DeRhamTopCup.bettiCupFrom A.variety _ n (Fin.init v)) (v (Fin.last n)) = _
      rw [ih]
      rfl

theorem exists_nonzero (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ∃ (u : H A.variety 0) (v : Fin (2 * A.variety.complexDimension) → H A.variety 1),
      DeRhamTopCup.cupFrom A.variety u (2 * A.variety.complexDimension) v ≠ 0 := by
  obtain ⟨v, hv⟩ := BettiTopCup.exists_nonzero A
  let u := (CechBettiEquivalence.algebraicEquiv A.variety 0).symm
    (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver))
  let w := fun i => (CechBettiEquivalence.algebraicEquiv A.variety 1).symm (v i)
  refine ⟨u, w, ?_⟩
  intro hz
  have he := comparison_cupFrom A.variety u (2 * A.variety.complexDimension) w
  simp only [u, w, LinearEquiv.apply_symm_apply, hz, map_zero, bettiCupFrom_unit] at he
  exact hv he.symm

theorem top_finrank (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Module.finrank ℂ (H A.variety (2 * A.variety.complexDimension)) = 1 := by
  rw [(CechBettiEquivalence.algebraicEquiv A.variety (2 * A.variety.complexDimension)).finrank_eq,
    AlgebraicGeometry.AbelianVariety.BettiNumbers.Constructions.ExteriorCohomology.abelian_complex_betti_number]
  exact Nat.choose_self _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DeRhamTopCup
