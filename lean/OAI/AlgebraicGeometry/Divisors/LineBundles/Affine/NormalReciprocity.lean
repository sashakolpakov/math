import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueBranchSum
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EulerBalance
import OAI.AlgebraicGeometry.Divisors.LineBundles.FactorialRationalReciprocity

/-! # Normal Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.NormalReciprocity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete rational residue reciprocity on a normal local surface

Each actual geometric residue divisor is the negative branch Euler
cycle. Their complete sum vanishes by the actual diagonal comparison.
Numerator/denominator representations and the proved bilinearity extend
this to every pair of nonzero rational functions, including shared
components and poles. No factoriality or properness is assumed.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open scoped Classical

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsLocalRing R]

theorem affineNormalRegularResidueBoundary_zero (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) = 0 := by
  let affineNormalReciprocity_dim : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdim.le
  rw [ResidueBranchSum.BundleCycles.affineRegularResidueBoundary_eq_branch_sum]
  have he (P : Branch.Diagonal.BundleCycles.minimalBranchIndex (a * b)) :
      ResidueCycleFamily.BundleCycles.normalResidueContribution (Spec (CommRingCat.of R)) (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
        (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) (ResidueBranchSum.BundleCycles.affineProductBranchEmbedding R a b ha hb P) =
      Finsupp.single (LocalDivisor.BundleCycles.affineLocalClosedPoint R) (-(Branch.FamilyEuler.BundleCycles.productBranchEuler a b ha hb P) : ℚ) :=
    ResidueBranchCycle.BundleCycles.affineNormalResidue_principal_eq_branchEuler R a b ha hb hdim P
  simp_rw [he]
  change (∑ P : Branch.Diagonal.BundleCycles.minimalBranchIndex (a * b),
    (Finsupp.singleAddHom (LocalDivisor.BundleCycles.affineLocalClosedPoint R)) (-(Branch.FamilyEuler.BundleCycles.productBranchEuler a b ha hb P) : ℚ)) = 0
  rw [← map_sum (Finsupp.singleAddHom (LocalDivisor.BundleCycles.affineLocalClosedPoint R))
    (fun P : Branch.Diagonal.BundleCycles.minimalBranchIndex (a * b) => (-(Branch.FamilyEuler.BundleCycles.productBranchEuler a b ha hb P) : ℚ)) Finset.univ]
  have hsum := congrArg (fun z : ℤ => (z : ℚ)) (Branch.EulerBalance.BundleCycles.productBranchEuler_sum_zero a b ha hb)
  rw [Int.cast_sum, Int.cast_zero] at hsum
  change Finsupp.single (LocalDivisor.BundleCycles.affineLocalClosedPoint R)
    (∑ P : Branch.Diagonal.BundleCycles.minimalBranchIndex (a * b), -(Branch.FamilyEuler.BundleCycles.productBranchEuler a b ha hb P : ℚ)) = 0
  rw [Finset.sum_neg_distrib, hsum, neg_zero, Finsupp.single_zero]

theorem affineNormalResidueBoundary_zero (hdim : ringKrullDim R = 2)
    (g h : (Spec (CommRingCat.of R)).functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R) g h = 0 := by
  obtain ⟨a, c, ha, hc, hg⟩ := FactorialRationalReciprocity.BundleCycles.affineFunctionUnit_exists_ratio R g
  obtain ⟨b, d, hb, hd, hh⟩ := FactorialRationalReciprocity.BundleCycles.affineFunctionUnit_exists_ratio R h
  rw [hg, hh, Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_left, Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    affineNormalRegularResidueBoundary_zero R a b ha hb hdim,
    affineNormalRegularResidueBoundary_zero R a d ha hd hdim,
    affineNormalRegularResidueBoundary_zero R c b hc hb hdim,
    affineNormalRegularResidueBoundary_zero R c d hc hd hdim]
  simp only [sub_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.NormalReciprocity.BundleCycles
