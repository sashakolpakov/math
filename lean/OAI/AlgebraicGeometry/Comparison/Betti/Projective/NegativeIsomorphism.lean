import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeHomology
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeTopCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentHomology
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop

/-! # Negative Isomorphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeIsomorphism.Dolbeault

noncomputable section

/-! The actual algebraic-to-analytic comparison is an isomorphism in positive top degree for every nonpositive twist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

def projectiveNegativeCycleAnalyticCoefficientEquiv (q k : ℕ) :
    SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles (R := ℂ) (σ := Fin (q + 2)) (-(k : ℤ)) (q + 1) ≃+
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (q + 2))) (-(k : ℤ)) :=
  (SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCyclesEquivCochain (R := ℂ) (-(k : ℤ)) (q + 1)).toAddEquiv.trans
    ((NegativeTopCoefficients.Dolbeault.projectiveFullNegativeTopCoefficientsEquiv (q + 1) k).toAddEquiv.trans
      (Algebraic.AnalyticNegativeCoefficients.Dolbeault.algebraicNegativeLaurentCoefficientEquiv (q + 2) k))

theorem projectiveLaurentOriginalComparison_top_negative_coordinates (q k : ℕ) (j : Fin (q + 2)) :
    (PositiveVanishing.Dolbeault.projectiveLaurentNegativeCyclesHomologyIso q j (-(k : ℤ))).hom ≫
      homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (q + 1) j (-(k : ℤ))) (q + 1) ≫
        (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCechHomologyIso q j (-(k : ℤ))).hom =
    (projectiveNegativeCycleAnalyticCoefficientEquiv q k).toAddCommGrpIso.hom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact NegativeHomology.Dolbeault.projectiveLaurentOriginalComparison_top_negative_homology q k j s

theorem projectiveLaurentOriginalComparison_top_nonpositive_isIso (q k : ℕ) (j : Fin (q + 2)) :
    IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (q + 1) j (-(k : ℤ))) (q + 1)) := by
  let A := PositiveVanishing.Dolbeault.projectiveLaurentNegativeCyclesHomologyIso q j (-(k : ℤ))
  let E := ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCechHomologyIso q j (-(k : ℤ))
  let C : AddCommGrpCat.of
      (SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles (R := ℂ) (σ := Fin (q + 2)) (-(k : ℤ)) (q + 1)) ≅
      AddCommGrpCat.of (HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (q + 2))) (-(k : ℤ))) :=
    (projectiveNegativeCycleAnalyticCoefficientEquiv q k).toAddCommGrpIso
  let I := A.symm ≪≫ C ≪≫ E.symm
  have h : homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (q + 1) j (-(k : ℤ))) (q + 1) = I.hom := by
    apply (cancel_epi A.hom).mp
    apply (cancel_mono E.hom).mp
    have hc := projectiveLaurentOriginalComparison_top_negative_coordinates q k j
    change A.hom ≫ _ ≫ E.hom = C.hom at hc
    simpa only [I, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using hc
  rw [h]
  infer_instance

theorem projectiveOriginalComparison_top_nonpositive_isIso (q k : ℕ) (j : Fin (q + 2)) :
    IsIso (homologyMap (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap (q + 1) j (-(k : ℤ))) (q + 1)) := by
  let := projectiveLaurentOriginalComparison_top_nonpositive_isIso q k j
  exact LaurentHomology.Dolbeault.projectiveOriginalComparison_isIso_of_laurent (q + 1) j (-(k : ℤ)) (q + 1)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeIsomorphism.Dolbeault
