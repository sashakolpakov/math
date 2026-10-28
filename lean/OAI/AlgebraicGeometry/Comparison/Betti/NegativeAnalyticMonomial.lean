import OAI.AlgebraicGeometry.Comparison.Betti.NormalizedPolynomialCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.AnalyticNegativeCoefficients

/-! # Negative Analytic Monomial -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NegativeAnalyticMonomial.Dolbeault

noncomputable section

section

/-! A single original negative Laurent coefficient is the corresponding actual analytic monomial. -/

open scoped BigOperators

local instance negativeAnalyticWeightDecidable (N k : ℕ) :
    DecidableEq (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) := Classical.decEq _

def negativeAnalyticMonomial (N k : ℕ) (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) (c : ℂ) :
    HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ)) :=
  NegativePolynomialCoefficientEquiv.Dolbeault.negativePolynomialCoefficientEquiv N k (NormalizedPolynomialCoefficients.Dolbeault.normalizedNegativeMonomial k e c)

theorem negativeAnalyticMonomial_coefficients (N k : ℕ)
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) (c : ℂ) :
    Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k (negativeAnalyticMonomial N k e c) = Pi.single e c := by
  change NormalizedPolynomialCoefficients.Dolbeault.normalizedPolynomialNegativeCoefficientEquiv k
    ((NegativePolynomialCoefficientEquiv.Dolbeault.negativePolynomialCoefficientEquiv N k).symm
      (NegativePolynomialCoefficientEquiv.Dolbeault.negativePolynomialCoefficientEquiv N k (NormalizedPolynomialCoefficients.Dolbeault.normalizedNegativeMonomial k e c))) = _
  rw [LinearEquiv.symm_apply_apply, NormalizedPolynomialCoefficients.Dolbeault.normalizedNegativeMonomial_coefficients]

theorem negativeAnalyticMonomial_apply (N k : ℕ)
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) (c : ℂ) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (negativeAnalyticMonomial N k e c).val x =
      c * ∏ i, x i ^ (-e.val.val i).toNat := by
  change MvPolynomial.eval x (MvPolynomial.monomial (NegativeLaurentMonomialExponents.Dolbeault.negativeToPositiveMonomialExponent k e).val c) = _
  rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  rfl

theorem negativeAnalyticMonomial_inverse_apply (N k : ℕ)
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) (c : ℂ) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction (negativeAnalyticMonomial N k e c).val
      (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates Finset.univ x) = c * ∏ i, x i ^ e.val.val i := by
  rw [negativeAnalyticMonomial_apply]
  apply congrArg (c * ·)
  apply Finset.prod_congr rfl
  intro i _
  simp only [Laurent.SectorTo.Dolbeault.laurentInverseCoordinates, Finset.mem_univ, ite_true]
  rw [← zpow_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent_lt k e i).le),
    inv_zpow, ← zpow_neg, neg_neg]

end

/-! Every actual full-negative analytic coefficient has its finite original Laurent expansion. -/

open scoped BigOperators

attribute [local instance] NormalizedPolynomialCoefficients.Dolbeault.fullNegativeMonomialExponent_finite

local instance negativeLaurentExpansionFintype (N k : ℕ) :
    Fintype (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) := Fintype.ofFinite _

local instance negativeLaurentExpansionDecidable (N k : ℕ) :
    DecidableEq (NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k) := Classical.decEq _

local instance negativeLaurentExpansionAddCommGroup (N k : ℕ) :
    AddCommGroup ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ))) :=
  Submodule.addCommGroup _

def homogeneousSectorCoefficientEvaluation {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (d : ℤ) (x : ι → ℂ) : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d →ₗ[ℂ] ℂ where
  toFun a := Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem negativeAnalyticCoefficient_expansion (N k : ℕ)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ))) :
    (∑ e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k,
      negativeAnalyticMonomial N k e (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k a e)) = a := by
  apply (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k).injective
  have hs := map_sum (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k).toAddEquiv.toAddMonoidHom
    (fun e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k =>
      negativeAnalyticMonomial N k e (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k a e)) Finset.univ
  refine hs.trans ?_
  exact (Finset.sum_congr rfl (fun e _ => negativeAnalyticMonomial_coefficients N k e
    (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k a e))).trans
      (Finset.univ_sum_single (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k a))

theorem negativeAnalyticCoefficient_inverse_expansion (N k : ℕ)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin N)) (-(k : ℤ))) (x : Fin N → ℂ) :
    Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates Finset.univ x) =
      ∑ e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k,
        Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k a e * ∏ i, x i ^ e.val.val i := by
  let E := homogeneousSectorCoefficientEvaluation (Finset.univ : Finset (Fin N)) (-(k : ℤ))
    (Laurent.SectorTo.Dolbeault.laurentInverseCoordinates Finset.univ x)
  have h := congrArg E (negativeAnalyticCoefficient_expansion N k a)
  rw [map_sum] at h
  have hs : (∑ e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k,
      E (negativeAnalyticMonomial N k e (Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k a e))) =
      ∑ e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin N) k,
        Algebraic.AnalyticNegativeCoefficients.Dolbeault.negativeAnalyticLaurentCoefficientEquiv N k a e * ∏ i, x i ^ e.val.val i := by
    apply Finset.sum_congr rfl
    intro e _
    exact negativeAnalyticMonomial_inverse_apply N k e _ x
  exact h.symm.trans hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.NegativeAnalyticMonomial.Dolbeault
