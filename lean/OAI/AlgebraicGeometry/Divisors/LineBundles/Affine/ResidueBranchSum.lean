import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueBranchCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueBoundaryAddition

/-! # Residue Branch Sum -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueBranchSum.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the complete affine residue boundary indexed by product branches

Every point in the actual residue support is a minimal prime of (ab).
The injective branch indexing therefore sums the entire intrinsic
residue family, including any shared components.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open scoped Classical

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

def affineProductBranchEmbedding (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Branch.Diagonal.BundleCycles.minimalBranchIndex (a * b) ↪ {x : Spec (CommRingCat.of R) // coheight x = 1} where
  toFun P := ⟨PrimeSupport.BundleCycles.affinePrimePoint R P.1, Divisor.BundleCycles.affineMinimalPrime_coheight (a * b) (mul_ne_zero ha hb) P.1 P.2⟩
  inj' _P _Q h := Subtype.ext (congrArg
    (fun z : {x : Spec (CommRingCat.of R) // coheight x = 1} => z.1.asIdeal) h)

omit [IsIntegrallyClosed R] in
theorem affineResidueSupport_mem_product_minimal (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : Spec (CommRingCat.of R))
    (hx : x ∈ Normal.PointResidue.BundleCycles.residueDivisorSupport (Spec (CommRingCat.of R)) (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb)) :
    x.asIdeal ∈ (Ideal.span {a * b}).minimalPrimes := by
  have hc := Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight (Spec (CommRingCat.of R))
    (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) ⟨x, hx⟩
  apply Divisor.BundleCycles.affineDivisorPoint_mem_minimal (a * b) (mul_ne_zero ha hb) x hc
  rcases Finset.mem_union.mp hx with hx | hx
  · have haP : a ∈ x.asIdeal := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hx) (Divisor.BundleCycles.affineRegularDivisor_eq_zero_of_not_mem a x hn)
    exact x.asIdeal.mul_mem_right b haP
  · have hbP : b ∈ x.asIdeal := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hx) (Divisor.BundleCycles.affineRegularDivisor_eq_zero_of_not_mem b x hn)
    exact x.asIdeal.mul_mem_left a hbP

theorem affineRegularResidueBoundary_eq_branch_sum (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) =
      ∑ P : Branch.Diagonal.BundleCycles.minimalBranchIndex (a * b),
        ResidueCycleFamily.BundleCycles.normalResidueContribution (Spec (CommRingCat.of R)) (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
          (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) (affineProductBranchEmbedding R a b ha hb P) := by
  let X := Spec (CommRingCat.of R)
  let g := ProperReciprocity.BundleCycles.affineFunctionUnit R a ha
  let h := ProperReciprocity.BundleCycles.affineFunctionUnit R b hb
  let i := affineProductBranchEmbedding R a b ha hb
  let F := ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R) g h
  have hs : (F.support : Set {x : X // coheight x = 1}) ⊆ Set.range i := by
    intro x hx
    have hxD : (x : X) ∈ Normal.PointResidue.BundleCycles.residueDivisorSupport X g h := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hx)
        (ResidueCycleFamily.BundleCycles.normalResidueContribution_eq_zero X (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R) g h x hn)
    have hP := affineResidueSupport_mem_product_minimal R a b ha hb x hxD
    exact ⟨⟨x.1.asIdeal, hP⟩, Subtype.ext rfl⟩
  exact (ResidueBoundaryAddition.BundleCycles.residueFamilySum_eq_boundary X (ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R) g h).symm.trans
    (Finite.FamilyReindex.BundleCycles.finiteFamily_sum_embedding i F hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueBranchSum.BundleCycles
