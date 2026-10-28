import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NonnegativeTwistAcyclic

/-! # Positive Isomorphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveIsomorphism.Dolbeault

noncomputable section

/-! The actual algebraic-to-analytic projective twist comparison is an isomorphism in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

theorem projectiveLaurentOriginalComparison_isIso_of_ne_top (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (q : ℕ) (hq : q + 1 ≠ n) :
    IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d) (q + 1)) := by
  have hA := AddCommGrpCat.isZero_iff_subsingleton.mpr
    (PositiveVanishing.Dolbeault.projectiveAlgebraicLaurent_homology_subsingleton_of_ne_top n j d q hq)
  have hB := (ProjectiveTwist.CechVanishing.Dolbeault.projectiveTwistCech_exactAt_of_ne_top n j d q hq).isZero_homology
  exact hA.isIso hB _

theorem projectiveTwistCech_homology_subsingleton_nonneg (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton (((cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj
      (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).homology (q + 1)) := by
  by_cases hq : q + 1 = n
  · subst n
    let : Subsingleton ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (q + 2))) d) :=
      NonnegativeTwistAcyclic.Dolbeault.fullNegativeCoefficients_subsingleton_nonneg d hd
    exact (ConcreteCategory.bijective_of_isIso (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCechHomologyIso q j d).hom).injective.subsingleton
  · exact AddCommGrpCat.isZero_iff_subsingleton.mp
      (ProjectiveTwist.CechVanishing.Dolbeault.projectiveTwistCech_exactAt_of_ne_top n j d q hq).isZero_homology

theorem projectiveLaurentOriginalComparison_nonneg_isIso (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d) (q + 1)) := by
  have hA := AddCommGrpCat.isZero_iff_subsingleton.mpr
    (PositiveVanishing.Dolbeault.projectiveAlgebraicLaurent_homology_subsingleton_nonneg n j d hd q)
  have hB := AddCommGrpCat.isZero_iff_subsingleton.mpr
    (projectiveTwistCech_homology_subsingleton_nonneg n j d hd q)
  exact hA.isIso hB _

theorem projectiveLaurentOriginalComparison_positive_isIso (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (q : ℕ) :
    IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j d) (q + 1)) := by
  by_cases hd : 0 ≤ d
  · exact projectiveLaurentOriginalComparison_nonneg_isIso n j d hd q
  · by_cases hq : q + 1 = n
    · subst n
      have hk : d = -(((-d).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega), neg_neg]
      rw [hk]
      exact NegativeIsomorphism.Dolbeault.projectiveLaurentOriginalComparison_top_nonpositive_isIso q (-d).toNat j
    · exact projectiveLaurentOriginalComparison_isIso_of_ne_top n j d q hq

theorem projectiveOriginalComparison_positive_isIso (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (q : ℕ) :
    IsIso (homologyMap (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d) (q + 1)) := by
  let := projectiveLaurentOriginalComparison_positive_isIso n j d q
  exact LaurentHomology.Dolbeault.projectiveOriginalComparison_isIso_of_laurent n j d (q + 1)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveIsomorphism.Dolbeault
