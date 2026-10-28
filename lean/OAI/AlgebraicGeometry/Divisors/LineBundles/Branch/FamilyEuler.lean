import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.Diagonal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ProductLength

/-! # Family Euler -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.FamilyEuler.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual Euler sum over all minimal branches
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

def productBranchEuler (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (P : Diagonal.BundleCycles.minimalBranchIndex (a * b)) : ℤ :=
  Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (PeriodicComplex.BundleCycles.productBranchPeriodicComplex a b P.1)
    (Diagonal.BundleCycles.productBranchPeriodicComplex_homology_length_ne_top a b ha hb P.1 P.2 false)
    (Diagonal.BundleCycles.productBranchPeriodicComplex_homology_length_ne_top a b ha hb P.1 P.2 true)

theorem productBranchFamily_homology_finite (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (j : Bool) :
    Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := Diagonal.BundleCycles.productBranchFamily a b) a b (Diagonal.BundleCycles.productBranchFamily_annihilated a b)).homology j) ≠ ⊤ :=
  Periodic.ProductLength.BundleCycles.periodicPiComplex_homology_finite
    (fun P : Diagonal.BundleCycles.minimalBranchIndex (a * b) => MultiplicationSequence.BundleCycles.equationEndomorphism a (PeriodicComplex.BundleCycles.productBranchModule a b P.1))
    (fun P : Diagonal.BundleCycles.minimalBranchIndex (a * b) => MultiplicationSequence.BundleCycles.equationEndomorphism b (PeriodicComplex.BundleCycles.productBranchModule a b P.1))
    (fun P => LocalizationImage.BundleCycles.localizationImage_equation_comp_zero P.1.primeCompl a b (ProductPeriodicComplex.BundleCycles.productEquation_comp_zero a b))
    (fun P => LocalizationImage.BundleCycles.localizationImage_equation_comp_zero P.1.primeCompl b a (ProductPeriodicComplex.BundleCycles.productEquation_comp_zero_reverse a b))
    (fun P j => Diagonal.BundleCycles.productBranchPeriodicComplex_homology_length_ne_top a b ha hb P.1 P.2 j) j

theorem productBranchFamily_Euler_sum (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := Diagonal.BundleCycles.productBranchFamily a b) a b (Diagonal.BundleCycles.productBranchFamily_annihilated a b))
      (productBranchFamily_homology_finite a b ha hb false)
      (productBranchFamily_homology_finite a b ha hb true) =
      ∑ P : Diagonal.BundleCycles.minimalBranchIndex (a * b), productBranchEuler a b ha hb P :=
  Periodic.ProductLength.BundleCycles.periodicPiEulerLength_sum
    (fun P : Diagonal.BundleCycles.minimalBranchIndex (a * b) => MultiplicationSequence.BundleCycles.equationEndomorphism a (PeriodicComplex.BundleCycles.productBranchModule a b P.1))
    (fun P : Diagonal.BundleCycles.minimalBranchIndex (a * b) => MultiplicationSequence.BundleCycles.equationEndomorphism b (PeriodicComplex.BundleCycles.productBranchModule a b P.1))
    (fun P => LocalizationImage.BundleCycles.localizationImage_equation_comp_zero P.1.primeCompl a b (ProductPeriodicComplex.BundleCycles.productEquation_comp_zero a b))
    (fun P => LocalizationImage.BundleCycles.localizationImage_equation_comp_zero P.1.primeCompl b a (ProductPeriodicComplex.BundleCycles.productEquation_comp_zero_reverse a b))
    (fun P => Diagonal.BundleCycles.productBranchPeriodicComplex_homology_length_ne_top a b ha hb P.1 P.2 false)
    (fun P => Diagonal.BundleCycles.productBranchPeriodicComplex_homology_length_ne_top a b ha hb P.1 P.2 true)
    (productBranchFamily_homology_finite a b ha hb false)
    (productBranchFamily_homology_finite a b ha hb true)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.FamilyEuler.BundleCycles
