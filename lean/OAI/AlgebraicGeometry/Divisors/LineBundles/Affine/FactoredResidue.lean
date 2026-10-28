import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.BranchFactorization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.FactoredResidue

/-! # Factored Residue -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FactoredResidue.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual affine normal residue function for cleared factors -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

local instance affineFactoredResidue_stalkNormal (P : Ideal R) [P.IsPrime] :
    IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P)) :=
  ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R (PrimeSupport.BundleCycles.affinePrimePoint R P)

theorem affineNormalResidueFunction_factored (P : Ideal R) [P.IsPrime]
    (hx : coheight (PrimeSupport.BundleCycles.affinePrimePoint R P) = 1)
    (a b t u s v w : R) (ha : a ≠ 0) (hb : b ≠ 0) (m n : ℕ)
    (ht : Irreducible (algebraMap R (Localization P.primeCompl) t))
    (hu : u ∉ P) (hs : s ∉ P) (hv : v ∉ P) (hw : w ∉ P)
    (hsa : s * a = u * t ^ m) (hwb : w * b = v * t ^ n) :
    Normal.PointResidue.BundleCycles.normalPointResidueFunction (Spec (CommRingCat.of R)) (PrimeSupport.BundleCycles.affinePrimePoint R P) hx
      (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) =
      (Principal.CartierCycle.BundleCycles.supportRegularFunction (Divisor.BundleCycles.affineAmbientSection R u) (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P)) /
        Principal.CartierCycle.BundleCycles.supportRegularFunction (Divisor.BundleCycles.affineAmbientSection R s) (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P))) ^ (n : ℤ) /
      (Principal.CartierCycle.BundleCycles.supportRegularFunction (Divisor.BundleCycles.affineAmbientSection R v) (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P)) /
        Principal.CartierCycle.BundleCycles.supportRegularFunction (Divisor.BundleCycles.affineAmbientSection R w) (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P))) ^ (m : ℤ) := by
  let X := Spec (CommRingCat.of R)
  let x := PrimeSupport.BundleCycles.affinePrimePoint R P
  let affineFactoredResidue_stalkDVR := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  let π := X.presheaf.germ ⊤ x (by trivial) (Divisor.BundleCycles.affineAmbientSection R t)
  have hπ : Irreducible π := BranchFactorization.BundleCycles.affineBranch_uniformizer_irreducible R P t ht
  rw [Normal.PointResidue.BundleCycles.normalPointResidueFunction_eq X x hx π hπ]
  exact Geometric.FactoredResidue.BundleCycles.geometricResidueFunction_of_quotient_factors X x π hπ
    (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb)
    (Divisor.BundleCycles.affineAmbientSection R u) (Divisor.BundleCycles.affineAmbientSection R s) (Divisor.BundleCycles.affineAmbientSection R v) (Divisor.BundleCycles.affineAmbientSection R w)
    (BranchFactorization.BundleCycles.affineBranchStalkUnit R P u hu) (BranchFactorization.BundleCycles.affineBranchStalkUnit R P s hs)
    (BranchFactorization.BundleCycles.affineBranchStalkUnit R P v hv) (BranchFactorization.BundleCycles.affineBranchStalkUnit R P w hw) m n
    (BranchFactorization.BundleCycles.affineBranchStalkUnit_val R P u hu) (BranchFactorization.BundleCycles.affineBranchStalkUnit_val R P s hs)
    (BranchFactorization.BundleCycles.affineBranchStalkUnit_val R P v hv) (BranchFactorization.BundleCycles.affineBranchStalkUnit_val R P w hw)
    (BranchFactorization.BundleCycles.affineFunctionUnit_branch_factor R P a t u s ha hu hs m hsa)
    (BranchFactorization.BundleCycles.affineFunctionUnit_branch_factor R P b t v w hb hv hw n hwb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FactoredResidue.BundleCycles
