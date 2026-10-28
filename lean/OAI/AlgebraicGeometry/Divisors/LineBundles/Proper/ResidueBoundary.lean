import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ResidueDifference
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Residue Boundary -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ResidueBoundary.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the complete proper residue boundary is the actual intersection difference

The finite union of the native divisor supports covers both Cartier
sums. At every point in that union, the proved proper-component formula
identifies the residue principal divisor with the corresponding difference.
Summing retains all coefficients of the actual cycles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order
open scoped Classical

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem principalCartierPointMap_divisor_sum (a : Γ(X, ⊤)) (g : X.functionField)
    (S : Finset X) (hs : (Ord.BundleCycles.principalDivisor X g).support ⊆ S) :
    Principal.CartierFiber.BundleCycles.principalCartierPointMap a (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
      ∑ x : S, (X.ord g x : ℚ) • Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm (x : X)) := by
  have hq : (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g).support ⊆ S := by
    intro x hx
    apply hs
    apply Finsupp.mem_support_iff.mpr
    intro hz
    apply Finsupp.mem_support_iff.mp hx
    change (Ord.BundleCycles.principalDivisor X g x : ℚ) = 0
    rw [hz, Int.cast_zero]
  rw [Principal.CartierFiber.BundleCycles.principalCartierPointMap, Finsupp.linearCombination_apply]
  exact ((RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g).sum_of_support_subset hq
    (fun x q => q • Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x))
    (fun x _ => zero_smul ℚ (Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x)))).trans
    (Finset.sum_coe_sort S (fun x : X => (X.ord g x : ℚ) •
      Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x))).symm

theorem normalResidueBoundaryCycle_proper
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (a b : Γ(X, ⊤))
    (hproper : ∀ x : X, coheight x = 1 →
      IsUnit (X.presheaf.germ ⊤ x (by trivial) a) ∨ IsUnit (X.presheaf.germ ⊤ x (by trivial) b))
    (g h : X.functionFieldˣ)
    (hg : (g : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X a)
    (hh : (h : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X b) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h =
      Principal.CartierFiber.BundleCycles.principalCartierPointMap a (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (h : X.functionField)) -
        Principal.CartierFiber.BundleCycles.principalCartierPointMap b (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (g : X.functionField)) := by
  rw [principalCartierPointMap_divisor_sum X a (h : X.functionField) (Normal.PointResidue.BundleCycles.residueDivisorSupport X g h)
      Finset.subset_union_right,
    principalCartierPointMap_divisor_sum X b (g : X.functionField) (Normal.PointResidue.BundleCycles.residueDivisorSupport X g h)
      Finset.subset_union_left, ← Finset.sum_sub_distrib]
  unfold Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle
  apply Finset.sum_congr rfl
  intro x _
  let := hNormal x
  have hx := Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight X g h x
  exact Normal.ResidueDifference.BundleCycles.normalResidue_principal_proper X x hx a b (hproper x hx) g h hg hh

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ResidueBoundary.BundleCycles
