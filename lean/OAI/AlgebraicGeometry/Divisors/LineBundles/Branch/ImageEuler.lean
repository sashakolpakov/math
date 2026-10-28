import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.ImageLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.SubmoduleEuler

/-! # Image Euler -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.ImageEuler.BundleCycles

noncomputable section

/-!
# LineBundleCycles: equation Euler values on actual differential images

The branch filtration formula applies to the actual differential
image, whose generic length has now been computed independently.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsLocalRing R]

local instance branchImageEulerAddCommGroup (a b r : R) (P : Ideal R) [P.IsPrime] :
    AddCommGroup (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range :=
  (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range.addCommGroup

local instance branchImageEulerModule (a b r : R) (P : Ideal R) [P.IsPrime] :
    Module R (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range :=
  (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range.module

theorem branchImage_equation_lengths_finite (a b r x : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {a * b}).minimalPrimes) (hx : x ∉ P) :
    Module.length R (MultiplicationSequence.BundleCycles.equationKernel x (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) ≠ ⊤ ∧
      Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) ≠ ⊤ :=
  SubmoduleEuler.BundleCycles.branchSubmodule_equation_lengths_finite (a * b) x (mul_ne_zero ha hb) hdim P hP hx _

theorem branchImage_equationEuler_eq_local_length (a b r x : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {a * b}).minimalPrimes) (hx : x ∉ P)
    (hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel x (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range) ≠ ⊤) :
    EquationEulerLength.BundleCycles.equationEulerLength x (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range hK hC =
      ((Module.length (Localization P.primeCompl)
        (LocalizedModule P.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range)).toNat : ℤ) *
          PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength x P :=
  SubmoduleEuler.BundleCycles.branchSubmoduleEquationEuler_eq_local_length (a * b) x (mul_ne_zero ha hb) hdim P hP hx _

def branchImageEuler (a b r x : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {a * b}).minimalPrimes) (hx : x ∉ P) : ℤ :=
  EquationEulerLength.BundleCycles.equationEulerLength x (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range
    (branchImage_equation_lengths_finite a b r x ha hb hdim P hP hx).1
    (branchImage_equation_lengths_finite a b r x ha hb hdim P hP hx).2

theorem branchImageEuler_eq_local_length (a b r x : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {a * b}).minimalPrimes) (hx : x ∉ P) :
    branchImageEuler a b r x ha hb hdim P hP hx =
      ((Module.length (Localization P.primeCompl)
        (LocalizedModule P.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism r (PeriodicComplex.BundleCycles.productBranchModule a b P)).range)).toNat : ℤ) *
          PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength x P :=
  branchImage_equationEuler_eq_local_length a b r x ha hb hdim P hP hx _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.ImageEuler.BundleCycles
