import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerExact
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProductEquationImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationImage

/-! # Image Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.ImageLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual local lengths of branch differential images

The localization and quotient equivalences identify the image of r
on a branch with its image in R_P/(rs). The latter is R_P/(s), so
its length is the actual local order of s.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

local instance branchLengthImageAddCommGroup (a b r : R) (P : Ideal R) [P.IsPrime] :
    AddCommGroup (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range :=
  (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range.addCommGroup

local instance branchLengthImageModule (a b r : R) (P : Ideal R) [P.IsPrime] :
    Module R (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range :=
  (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range.module

def branchQuotientLocalEquivAlgebra (a b : R) (P : Ideal R) [P.IsPrime]
    (J : Ideal (Localization P.primeCompl))
    (hJ : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) = J) :
    LocalizedModule P.primeCompl (PeriodicComplex.BundleCycles.productBranchModule a b P) ≃ₗ[Localization P.primeCompl]
      (Localization P.primeCompl) ⧸ J :=
  (PowerExact.BundleCycles.branchQuotientLocalEquiv a b P J hJ).extendScalarsOfIsLocalization P.primeCompl (Localization P.primeCompl)

theorem branchImage_local_length (a b r s : R) (P : Ideal R) [P.IsPrime]
    (hr : algebraMap R (Localization P.primeCompl) r ≠ 0)
    (hJ : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {algebraMap R (Localization P.primeCompl) r * algebraMap R (Localization P.primeCompl) s}) :
    Module.length (Localization P.primeCompl)
        (LocalizedModule P.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) =
      Ring.ord (Localization P.primeCompl) (algebraMap R (Localization P.primeCompl) s) := by
  let A := Localization P.primeCompl
  let α := algebraMap R A r
  let β := algebraMap R A s
  let e := branchQuotientLocalEquivAlgebra a b P (Ideal.span {α * β}) hJ
  exact ((LocalizedEquationImage.BundleCycles.localizedEquationRangeEquiv (M := PeriodicComplex.BundleCycles.productBranchModule a b P) P.primeCompl r).trans
    ((LocalizedEquationImage.BundleCycles.equationRangeEquiv α e).trans (ProductEquationImage.BundleCycles.productEquationImageEquiv α β hr))).length_eq

theorem productBranchImage_local_length_left (a b : R) (ha : a ≠ 0) (P : Ideal R) [P.IsPrime] :
    Module.length (Localization P.primeCompl)
        (LocalizedModule P.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism a (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) =
      Ring.ord (Localization P.primeCompl) (algebraMap R (Localization P.primeCompl) b) := by
  apply branchImage_local_length a b a b P
  · exact (map_ne_zero_iff _ (IsLocalization.injective (Localization P.primeCompl)
      P.primeCompl_le_nonZeroDivisors)).mpr ha
  · rw [Ideal.map_span, Set.image_singleton, map_mul]

theorem productBranchImage_local_length_right (a b : R) (hb : b ≠ 0) (P : Ideal R) [P.IsPrime] :
    Module.length (Localization P.primeCompl)
        (LocalizedModule P.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism b (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) =
      Ring.ord (Localization P.primeCompl) (algebraMap R (Localization P.primeCompl) a) := by
  apply branchImage_local_length a b b a P
  · exact (map_ne_zero_iff _ (IsLocalization.injective (Localization P.primeCompl)
      P.primeCompl_le_nonZeroDivisors)).mpr hb
  · rw [Ideal.map_span, Set.image_singleton, map_mul]
    exact congrArg (fun z : Localization P.primeCompl => Ideal.span {z}) (mul_comm _ _)

theorem branchPowersImage_local_length (a b t : R) (m n : ℕ) (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization P.primeCompl)]
    (ht : Irreducible (algebraMap R (Localization P.primeCompl) t))
    (hI : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.primeCompl) t) ^ (m + n)}) :
    Module.length (Localization P.primeCompl)
        (LocalizedModule P.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism (t ^ m) (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) = n := by
  let A := Localization P.primeCompl
  have hprod : algebraMap R A (t ^ m) * algebraMap R A (t ^ n) = (algebraMap R A t) ^ (m + n) := by
    rw [map_pow, map_pow, ← pow_add]
  have hJ : (Ideal.span {a * b}).map (algebraMap R A) =
      Ideal.span {algebraMap R A (t ^ m) * algebraMap R A (t ^ n)} :=
    hI.trans (congrArg (fun z : A => Ideal.span {z}) hprod.symm)
  have hr : algebraMap R A (t ^ m) ≠ 0 := by rw [map_pow]; exact pow_ne_zero m ht.ne_zero
  rw [branchImage_local_length a b (t ^ m) (t ^ n) P hr hJ, map_pow,
    Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero), Ring.ord_of_irreducible ht]
  simp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.ImageLength.BundleCycles
