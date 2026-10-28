import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NonnegativeZero
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeZeroCycles
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.NegativeCoefficientVanishing

/-! # Isomorphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Isomorphism.Dolbeault

noncomputable section

/-! The actual projective twist comparison is an isomorphism in every degree on positive-dimensional projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

theorem projectiveTwistZeroCycles_subsingleton_neg (n : ℕ) (j : Fin (n + 2)) (d : ℤ) (hd : d < 0) :
    Subsingleton (ZeroCycles.Dolbeault.projectiveTwistZeroCycles (n + 1) j d) := by
  let : Subsingleton ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 2))) d) :=
    ⟨fun a b => (NegativeCoefficientVanishing.Dolbeault.positiveCoefficient_zero_neg d hd a).trans (NegativeCoefficientVanishing.Dolbeault.positiveCoefficient_zero_neg d hd b).symm⟩
  exact (ZeroCycles.Dolbeault.projectiveTwistZeroCycleCoefficientEquiv n j d).injective.subsingleton

theorem projectiveLaurentOriginalComparison_zero_negative_isIso (n : ℕ) (j : Fin (n + 2))
    (d : ℤ) (hd : d < 0) :
    IsIso (homologyMap (Projective.LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (n + 1) j d) 0) := by
  let := Projective.NegativeZeroCycles.Dolbeault.projectiveLaurentZeroCycles_subsingleton_neg n d hd
  let : Subsingleton (((Projective.LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex (n + 1) j d).d 0 1).hom.ker) :=
    (Projective.ZeroCycleModel.Dolbeault.projectiveLaurentZeroCyclesEquiv (n + 1) j d).injective.subsingleton
  let := projectiveTwistZeroCycles_subsingleton_neg n j d hd
  apply AdditiveHomology.Cech.additiveHZeroMap_isIso_of_zeroCycles
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem projectiveLaurentOriginalComparison_all_degrees_isIso (n : ℕ) (j : Fin (n + 2))
    (d : ℤ) (r : ℕ) :
    IsIso (homologyMap (Projective.LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (n + 1) j d) r) := by
  cases r with
  | zero =>
    by_cases hd : 0 ≤ d
    · have he : d = (d.toNat : ℤ) := (Int.toNat_of_nonneg hd).symm
      rw [he]
      exact Projective.NonnegativeZero.Dolbeault.projectiveLaurentOriginalComparison_zero_nonnegative_isIso n d.toNat j
    · exact projectiveLaurentOriginalComparison_zero_negative_isIso n j d (lt_of_not_ge hd)
  | succ q => exact Projective.PositiveIsomorphism.Dolbeault.projectiveLaurentOriginalComparison_positive_isIso (n + 1) j d q

theorem projectiveOriginalComparison_all_degrees_isIso (n : ℕ) (j : Fin (n + 2))
    (d : ℤ) (r : ℕ) :
    IsIso (homologyMap (ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap (n + 1) j d) r) := by
  let := projectiveLaurentOriginalComparison_all_degrees_isIso n j d r
  exact Projective.LaurentHomology.Dolbeault.projectiveOriginalComparison_isIso_of_laurent (n + 1) j d r

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Isomorphism.Dolbeault
