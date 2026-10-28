import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.FamilyEuler
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.Diagonal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FiniteError

/-! # Euler Balance -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EulerBalance.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the total Euler contribution of the actual branch complexes is zero

The exact product complex has zero Euler invariant. Its actual diagonal
to all branch images has finite-length kernel and cokernel, whose Euler
invariants vanish. The full branch sum therefore vanishes as an integer.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

theorem productBranchEuler_sum_zero (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ P : Diagonal.BundleCycles.minimalBranchIndex (a * b), FamilyEuler.BundleCycles.productBranchEuler a b ha hb P = 0 := by
  have hM (j : Bool) : Module.length R ((ProductPeriodicComplex.BundleCycles.productPeriodicComplex a b).homology j) ≠ ⊤ := by
    rw [ProductPeriodicComplex.BundleCycles.productPeriodicComplex_homology_length_zero a b ha hb j]
    exact ENat.zero_ne_top
  have he := Periodic.FiniteError.BundleCycles.equationPeriodicEulerLength_eq_of_finite_errors
    (M := ProductPeriodicComplex.BundleCycles.productEquationQuotient a b) (N := Diagonal.BundleCycles.productBranchFamily a b) a b
    (Diagonal.BundleCycles.productEquation_annihilated a b) (Diagonal.BundleCycles.productBranchFamily_annihilated a b)
    (Diagonal.BundleCycles.productBranchDiagonal a b)
    (Diagonal.BundleCycles.productBranchDiagonal_kernel_length_ne_top a b ha hb)
    (Diagonal.BundleCycles.productBranchDiagonal_cokernel_length_ne_top a b ha hb)
    (hM false) (hM true)
    (FamilyEuler.BundleCycles.productBranchFamily_homology_finite a b ha hb false)
    (FamilyEuler.BundleCycles.productBranchFamily_homology_finite a b ha hb true)
  exact (FamilyEuler.BundleCycles.productBranchFamily_Euler_sum a b ha hb).symm.trans
    (he.symm.trans (ProductPeriodicComplex.BundleCycles.productPeriodicEulerLength_zero a b ha hb (hM false) (hM true)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EulerBalance.BundleCycles
