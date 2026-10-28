import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.FiltrationWeight
import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationUnitLength

/-! # Equation Euler -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EquationEuler.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the one-equation Euler length on an actual branch module

For a finite module with annihilator radical P, its multiplication
Euler length is its actual length at P times the equation order on
R/P. An auxiliary annihilator, constructed by prime avoidance, lets
the proved two-equation prime-filtration formula supply the result.
-/

variable {R : Type*} [CommRing R]

private theorem branchWeight_list_sum (L : List (Ideal R)) (P : Ideal R) (w : ℤ) :
    (L.map (fun J => if J = P then w else 0)).sum = (L.count P : ℤ) * w := by
  classical
  induction L with
  | nil => simp
  | cons J L ih =>
    by_cases he : J = P
    · subst J
      simp [ih, add_mul, add_comm]
    · simp [he, ih]

variable {M : Type*} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsDomain R] [IsLocalRing R] [Module.Finite R M]

theorem equationEulerLength_branch_formula (r x : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {r}).minimalPrimes)
    (hAnn : (Module.annihilator R M).radical = P) (hxP : x ∉ P)
    (hK : Module.length R (MultiplicationSequence.BundleCycles.equationKernel x M) ≠ ⊤)
    (hC : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x M) ≠ ⊤) :
    EquationEulerLength.BundleCycles.equationEulerLength x M hK hC =
      ((Module.length (Localization P.primeCompl) (LocalizedModule P.primeCompl M)).toNat : ℤ) *
        PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength x P := by
  classical
  by_cases hxunit : IsUnit x
  · rw [EquationUnitLength.BundleCycles.equationEulerLength_zero_of_unit x hxunit, EquationUnitLength.BundleCycles.primeIntersectionQuotientLength_unit x hxunit, mul_zero]
  let branchEulerDimension : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdim.le
  obtain ⟨y, hyI, hy, hxy⟩ := AuxiliaryParameter.BundleCycles.branchIdeal_exists_proper_parameter r x hr hdim P
    (Module.annihilator R M) hP hAnn hxP hxunit
  have hyM : Module.IsTorsionBy R M y := fun {m} => Module.mem_annihilator.mp hyI m
  have hyP : y ∈ P := hAnn ▸ Ideal.le_radical hyI
  have hPy : P ∈ (Ideal.span {y}).minimalPrimes :=
    (SurfacePrimeFactors.BundleCycles.surfacePrime_minimal_or_maximal y hy P hyP).resolve_right
      (AuxiliaryParameter.BundleCycles.minimalPrincipalPrime_ne_maximal r hdim P hP)
  let F := PrimeFiltration.BundleCycles.modulePrimeFiltration (R := R) (M := M)
  have hbase : EquationEulerLength.BundleCycles.equationEulerLength x M hK hC =
      (F.factors.map (SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight x y)).sum :=
    (F.whole_eulerSum_eq x y (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hxy) hyM).symm.trans
      (F.surface_eulerSum_eq x y hy hdim hxy hyM)
  have hweights : F.factors.map (SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight x y) =
      F.factors.map (fun J => if J = P then PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength x P else 0) := by
    apply List.map_congr_left
    intro J hJ
    exact FiltrationWeight.BundleCycles.branchFiltration_weight r x y hr hdim P hP hPy hAnn F J hJ
  have hlen : (Module.length (Localization P.primeCompl) (LocalizedModule P.primeCompl M)).toNat =
      F.factors.count P := by
    rw [F.whole_localized_length_eq_count y hyM P hPy, ENat.toNat_natCast]
  rw [hbase, hweights, branchWeight_list_sum, hlen]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EquationEuler.BundleCycles
