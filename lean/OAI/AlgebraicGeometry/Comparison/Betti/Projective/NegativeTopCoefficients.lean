import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeWeightResidue
import OAI.AlgebraicGeometry.Comparison.Betti.NegativeAnalyticMonomial
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport

/-! # Negative Top Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeTopCoefficients.Dolbeault

noncomputable section

section

/-! The original comparison has the canonical coefficient map on every full-negative assembly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules
open scoped BigOperators

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup
attribute [local instance] NormalizedPolynomialCoefficients.Dolbeault.fullNegativeMonomialExponent_finite

local instance (N k : ℕ) : Fintype (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) := Fintype.ofFinite _

def projectiveFullNegativeTopCoefficients (n k : ℕ)
    (s : SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain (R := ℂ) (σ := Fin (n + 1)) (-(k : ℤ)) n) :
    NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k → Γ(Spec (CommRingCat.of ℂ), ⊤) :=
  fun e => (s e).val (NegativeMonomialResidue.Dolbeault.projectiveOrderedTopTuple n)

theorem projectiveLaurentOriginalComparison_top_negative_assembly (n k : ℕ) (j : Fin (n + 1))
    (s : SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain (R := ℂ) (σ := Fin (n + 1)) (-(k : ℤ)) n) :
    ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue n j (-(k : ℤ))
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (-(k : ℤ))).f n
        (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly (R := ℂ) (-(k : ℤ)) n s)) =
      Algebraic.AnalyticNegativeCoefficients.Dolbeault.algebraicNegativeLaurentCoefficientEquiv (n + 1) k (projectiveFullNegativeTopCoefficients n k s) := by
  let F : (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j (-(k : ℤ))).X n →+
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (n + 1))) (-(k : ℤ)) :=
    (ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue n j (-(k : ℤ))).comp
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (-(k : ℤ))).f n).hom
  let a := Algebraic.AnalyticNegativeCoefficients.Dolbeault.algebraicNegativeLaurentCoefficientEquiv (n + 1) k
    (projectiveFullNegativeTopCoefficients n k s)
  have hs : SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly (R := ℂ) (-(k : ℤ)) n s =
      ∑ e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k,
        SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := ℂ) (-(k : ℤ)) e.val n (s e) :=
    SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly_apply (R := ℂ) (-(k : ℤ)) n s
  change F (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly (R := ℂ) (-(k : ℤ)) n s) = a
  refine (congrArg F hs).trans ?_
  refine (map_sum F (fun e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k =>
    (SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := ℂ) (-(k : ℤ)) e.val n (s e) :
      (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j (-(k : ℤ))).X n)) Finset.univ).trans ?_
  calc
    _ = ∑ e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k,
        NegativeAnalyticMonomial.Dolbeault.negativeAnalyticMonomial (n + 1) k e
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (projectiveFullNegativeTopCoefficients n k s e)) := by
      apply Finset.sum_congr rfl
      intro e _
      exact NegativeWeightResidue.Dolbeault.projectiveLaurentOriginalComparison_top_negative_weight n k j e (s e)
    _ = ∑ e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k,
        NegativeAnalyticMonomial.Dolbeault.negativeAnalyticMonomial (n + 1) k e (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv (n + 1) k a e) := by
      apply Finset.sum_congr rfl
      intro e _
      exact congrArg (NegativeAnalyticMonomial.Dolbeault.negativeAnalyticMonomial (n + 1) k e)
        (Algebraic.AnalyticNegativeCoefficients.Dolbeault.algebraicNegativeLaurentCoefficientEquiv_coefficient (n + 1) k
          (projectiveFullNegativeTopCoefficients n k s) e).symm
    _ = a := NegativeAnalyticMonomial.Dolbeault.negativeAnalyticCoefficient_expansion (n + 1) k a

end

/-! Evaluation on the actual ordered top tuple identifies all original full-negative cochains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules

theorem projectiveOrderedTopTuple_unique (n : ℕ)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{0} (Fin (n + 1))) n) : a = NegativeMonomialResidue.Dolbeault.projectiveOrderedTopTuple n := by
  have hn : Fintype.card (ULift.{0} (Fin (n + 1))) = n + 1 := by simp
  exact (SheafCohomology.Projective.OrderedCechTopSupport.orderedCechTopIndex_unique n hn a).trans
    (SheafCohomology.Projective.OrderedCechTopSupport.orderedCechTopIndex_unique n hn (NegativeMonomialResidue.Dolbeault.projectiveOrderedTopTuple n)).symm

def projectiveFullNegativeTopCoefficientsEquiv (n k : ℕ) :
    SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain (R := ℂ) (σ := Fin (n + 1)) (-(k : ℤ)) n ≃ₗ[
      Γ(Spec (CommRingCat.of ℂ), ⊤)]
        (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k → Γ(Spec (CommRingCat.of ℂ), ⊤)) where
  toFun := projectiveFullNegativeTopCoefficients n k
  invFun a e := ⟨fun _ => a e, fun t ht =>
    (ht (fun x _ => SheafCohomology.Projective.OrderedCechTopSupport.orderedCechTopIndex_surjective n (by simp) t x)).elim⟩
  left_inv s := by
    funext e
    apply Subtype.ext
    funext t
    exact congrArg (s e).val (projectiveOrderedTopTuple_unique n t).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeTopCoefficients.Dolbeault
