import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.TopCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.NegativeCoefficientVanishing

/-! # Nonnegative Twist Acyclic -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NonnegativeTwistAcyclic.Dolbeault

noncomputable section

/-! Every actual analytified nonnegative projective twist is acyclic in positive degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup

theorem fullNegativeCoefficients_subsingleton_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (d : ℤ) (hd : 0 ≤ d) :
    Subsingleton ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset ι) d) :=
  ⟨fun a b => (NegativeCoefficientVanishing.Dolbeault.fullNegativeCoefficient_zero_nonneg d hd a).trans
    (NegativeCoefficientVanishing.Dolbeault.fullNegativeCoefficient_zero_nonneg d hd b).symm⟩

theorem projectiveNonnegativeTwist_cohomology_vanish (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton (Sheaf.H.{0} (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d) (q + 1)) := by
  by_cases hq : q + 1 = n
  · subst n
    let : Subsingleton ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset (Fin (q + 2))) d) :=
      fullNegativeCoefficients_subsingleton_nonneg d hd
    exact (ConcreteCategory.bijective_of_isIso (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCohomologyIso q j d).hom).injective.subsingleton
  · exact ProjectiveTwist.CechVanishing.Dolbeault.projectiveTwist_cohomology_vanish_of_ne_top n j d q hq

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NonnegativeTwistAcyclic.Dolbeault
