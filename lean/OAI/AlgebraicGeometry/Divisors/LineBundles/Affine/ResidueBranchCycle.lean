import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FactoredResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeRatioDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EulerEq

/-! # Residue Branch Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueBranchCycle.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the geometric residue divisor is the negative branch Euler cycle

The actual normal residue function is the quotient of the two restricted
unit ratios to the opposite exponents. Its complete principal divisor
recovers exactly the previously computed branch Euler coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsLocalRing R]

local instance affineResidueBranchCycle_stalkNormal (P : Ideal R) [P.IsPrime] :
    IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P)) :=
  ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R (PrimeSupport.BundleCycles.affinePrimePoint R P)

theorem affineNormalResidue_principal_factored (a b t u s v w : R)
    (ha : a ≠ 0) (hb : b ≠ 0) (hdim : ringKrullDim R = 2) (m n : ℕ)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {a * b}).minimalPrimes)
    (ht : Irreducible (algebraMap R (Localization P.primeCompl) t))
    (hu : u ∉ P) (hs : s ∉ P) (hv : v ∉ P) (hw : w ∉ P)
    (hsa : s * a = u * t ^ m) (hwb : w * b = v * t ^ n) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P))
      (Normal.PointResidue.BundleCycles.normalPointResidueFunction (Spec (CommRingCat.of R)) (PrimeSupport.BundleCycles.affinePrimePoint R P)
        (Divisor.BundleCycles.affineMinimalPrime_coheight (a * b) (mul_ne_zero ha hb) P hP)
        (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb)) =
      Finsupp.single (LocalDivisor.BundleCycles.affineLocalClosedPoint R)
        ((n : ℚ) * ((PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength u P : ℚ) - (PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength s P : ℚ)) -
        (m : ℚ) * ((PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength v P : ℚ) - (PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength w P : ℚ))) := by
  let W := irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P)
  have hus := div_ne_zero (PrimeRatioDivisor.BundleCycles.affineSupportRegularFunction_ne_zero R P u hu)
    (PrimeRatioDivisor.BundleCycles.affineSupportRegularFunction_ne_zero R P s hs)
  have hvw := div_ne_zero (PrimeRatioDivisor.BundleCycles.affineSupportRegularFunction_ne_zero R P v hv)
    (PrimeRatioDivisor.BundleCycles.affineSupportRegularFunction_ne_zero R P w hw)
  rw [FactoredResidue.BundleCycles.affineNormalResidueFunction_factored R P _ a b t u s v w ha hb m n ht hu hs hv hw hsa hwb,
    Support.PrincipalQuotients.BundleCycles.schemePrincipalPointDivisor_zpow_div W _ _ hus hvw (m : ℤ) (n : ℤ),
    PrimeRatioDivisor.BundleCycles.affinePrimeSupportRatio_divisor R u s (a * b) (mul_ne_zero ha hb) hdim P hP hu hs,
    PrimeRatioDivisor.BundleCycles.affinePrimeSupportRatio_divisor R v w (a * b) (mul_ne_zero ha hb) hdim P hP hv hw]
  simp only [Finsupp.smul_single, zsmul_eq_mul, Int.cast_natCast, ← Finsupp.single_sub]

variable [Ring.KrullDimLE 2 R]

theorem affineNormalResidue_principal_eq_branchEuler (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Branch.Diagonal.BundleCycles.minimalBranchIndex (a * b)) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P.1))
      (Normal.PointResidue.BundleCycles.normalPointResidueFunction (Spec (CommRingCat.of R)) (PrimeSupport.BundleCycles.affinePrimePoint R P.1)
        (Divisor.BundleCycles.affineMinimalPrime_coheight (a * b) (mul_ne_zero ha hb) P.1 P.2)
        (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (ProperReciprocity.BundleCycles.affineFunctionUnit R b hb)) =
      Finsupp.single (LocalDivisor.BundleCycles.affineLocalClosedPoint R) (-(Branch.FamilyEuler.BundleCycles.productBranchEuler a b ha hb P) : ℚ) := by
  let affineResidueBranchCycle_localDVR := Normal.PrimeDVR.BundleCycles.normalMinimalPrime_isDVR (a * b) (mul_ne_zero ha hb) P.1 P.2
  obtain ⟨t, _, ht⟩ := Normal.PrimeDVR.BundleCycles.exists_originalRing_uniformizer P.1
  obtain ⟨m, u, s, hu, hs, hsa, _⟩ := Branch.RegularFactorization.BundleCycles.branchRegular_factorization P.1 t ht a ha
  obtain ⟨n, v, w, hv, hw, hwb, _⟩ := Branch.RegularFactorization.BundleCycles.branchRegular_factorization P.1 t ht b hb
  rw [affineNormalResidue_principal_factored R a b t u s v w ha hb hdim m n P.1 P.2 ht hu hs hv hw hsa hwb,
    Branch.EulerEq.BundleCycles.productBranchEuler_eq_factor_orders a b t u s v w ha hb hdim m n P ht hu hs hv hw hsa hwb]
  apply congrArg (Finsupp.single (LocalDivisor.BundleCycles.affineLocalClosedPoint R))
  push_cast
  ring

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueBranchCycle.BundleCycles
