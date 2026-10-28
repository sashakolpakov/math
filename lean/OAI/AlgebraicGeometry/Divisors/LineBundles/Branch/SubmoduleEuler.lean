import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.SubmoduleAnnihilator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EquationFiniteness

/-! # Submodule Euler -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.SubmoduleEuler.BundleCycles

noncomputable section

/-!
# LineBundleCycles: one-equation Euler coefficients on actual branch submodules

This applies to the images of the two periodic differentials. The
zero submodule is included; every nonzero submodule has the already
computed branch annihilator radical, which supplies both finiteness
and the local-length coefficient formula.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsLocalRing R]

abbrev principalBranchImage (r : R) (P : Ideal R) [P.IsPrime] :=
  LocalizationImage.BundleCycles.localizationImage P.primeCompl (R ⧸ (Ideal.span ({r} : Set R)))

local instance branchEulerSubmoduleAddCommGroup (r : R) (P : Ideal R) [P.IsPrime]
    (N : Submodule R (principalBranchImage r P)) : AddCommGroup N := N.addCommGroup

local instance branchEulerSubmoduleModule (r : R) (P : Ideal R) [P.IsPrime]
    (N : Submodule R (principalBranchImage r P)) : Module R N := N.module

theorem branchSubmodule_equation_lengths_finite (r x : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {r}).minimalPrimes) (hxP : x ∉ P)
    (N : Submodule R (principalBranchImage r P)) :
    Module.length R (MultiplicationSequence.BundleCycles.equationKernel x N) ≠ ⊤ ∧ Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x N) ≠ ⊤ := by
  by_cases hN : Subsingleton N
  · let branchEquationTrivialSubmodule : Subsingleton N := hN
    have hlen : Module.length R N ≠ ⊤ := by rw [Module.length_eq_zero]; exact ENat.zero_ne_top
    exact ⟨EquationEulerLength.BundleCycles.equationKernel_length_ne_top x N hlen, EquationEulerLength.BundleCycles.equationCokernel_length_ne_top x N hlen⟩
  · let branchEquationNontrivialSubmodule : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
    exact EquationFiniteness.BundleCycles.branchEquation_lengths_finite (M := N) r x hr hdim P hP
      (SubmoduleAnnihilator.BundleCycles.localizationImage_submodule_annihilator_radical (Ideal.span {r}) P hP N) hxP

def branchSubmoduleEquationEuler (r x : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {r}).minimalPrimes) (hxP : x ∉ P)
    (N : Submodule R (principalBranchImage r P)) : ℤ :=
  EquationEulerLength.BundleCycles.equationEulerLength x N
    (branchSubmodule_equation_lengths_finite r x hr hdim P hP hxP N).1
    (branchSubmodule_equation_lengths_finite r x hr hdim P hP hxP N).2

theorem branchSubmoduleEquationEuler_eq_local_length (r x : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {r}).minimalPrimes) (hxP : x ∉ P)
    (N : Submodule R (principalBranchImage r P)) :
    branchSubmoduleEquationEuler r x hr hdim P hP hxP N =
      ((Module.length (Localization P.primeCompl) (LocalizedModule P.primeCompl N)).toNat : ℤ) *
        PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength x P := by
  by_cases hN : Subsingleton N
  · let branchEulerTrivialSubmodule : Subsingleton N := hN
    let branchEulerTrivialLocalization : Subsingleton (LocalizedModule P.primeCompl N) :=
      LocalizedModule.subsingleton_iff.mpr (fun m =>
        ⟨1, P.primeCompl.one_mem, (one_smul R m).trans (hN.elim m 0)⟩)
    have hlen : Module.length R N ≠ ⊤ := by rw [Module.length_eq_zero]; exact ENat.zero_ne_top
    calc
      branchSubmoduleEquationEuler r x hr hdim P hP hxP N = 0 :=
        EquationEulerLength.BundleCycles.equationEulerLength_zero_of_finite x N _ _ hlen
      _ = _ := by rw [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, zero_mul]
  · let branchEulerNontrivialSubmodule : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
    exact EquationEuler.BundleCycles.equationEulerLength_branch_formula (M := N) r x hr hdim P hP
      (SubmoduleAnnihilator.BundleCycles.localizationImage_submodule_annihilator_radical (Ideal.span {r}) P hP N) hxP _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.SubmoduleEuler.BundleCycles
