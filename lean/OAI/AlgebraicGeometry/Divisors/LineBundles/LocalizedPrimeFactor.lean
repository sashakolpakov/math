import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedFiltrationLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltrationEuler
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Localized Prime Factor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedPrimeFactor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: lengths of localized prime cyclic factors

A cyclic factor R/J vanishes after localization at P when J is not
contained in P. The factor R/P becomes the residue field and has length
one. These are identifications of the actual localized modules.
-/

variable {R : Type*} [CommRing R]

theorem idealQuotient_annihilated (J : Ideal R) (b : R) (hb : b ∈ J) :
    Module.IsTorsionBy R (R ⧸ J) b :=
  (Module.isTorsionBy_quotient_iff J b).mpr (fun x => J.mul_mem_right x hb)

theorem annihilator_mem_ideal (J : Ideal R) (b : R)
    (hb : Module.IsTorsionBy R (R ⧸ J) b) : b ∈ J := by
  have h := (Module.isTorsionBy_quotient_iff J b).mp hb (1 : R)
  simpa only [smul_eq_mul, mul_one] using h

variable (P : Ideal R) [P.IsPrime]

theorem localizedPrimeFactorLength_zero (J : Ideal R) (hJP : ¬ J ≤ P) :
    LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength P.primeCompl J = 0 := by
  obtain ⟨b, hbJ, hbP⟩ := SetLike.not_le_iff_exists.mp hJP
  let : Subsingleton (LocalizedModule P.primeCompl (R ⧸ J)) :=
    LocalizedModule.subsingleton_iff.mpr (fun m =>
      ⟨b, hbP, @idealQuotient_annihilated R _ J b hbJ m⟩)
  exact Module.length_eq_zero

/-- The actual localization of R/P is the residue quotient of R_P. -/
def localizedPrimeResidueEquiv :
    LocalizedModule P.primeCompl (R ⧸ P) ≃ₗ[Localization P.primeCompl]
      (Localization P.primeCompl) ⧸ IsLocalRing.maximalIdeal (Localization P.primeCompl) := by
  let A := Localization P.primeCompl
  let L := P.localized' A P.primeCompl (Algebra.linearMap R A)
  have hL : L = IsLocalRing.maximalIdeal A := by
    dsimp only [L]
    rw [Submodule.localized'_eq_span]
    exact Localization.AtPrime.map_eq_maximalIdeal
  let e : LocalizedModule P.primeCompl (R ⧸ P) ≃ₗ[R] A ⧸ L :=
    IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap _ _)
      (P.toLocalizedQuotient' A P.primeCompl (Algebra.linearMap R A))
  exact (e.extendScalarsOfIsLocalization P.primeCompl A).trans
    (Submodule.quotEquivOfEq _ _ hL)

theorem localizedPrimeFactorLength_self : LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength P.primeCompl P = 1 := by
  let : IsSimpleModule (Localization P.primeCompl)
      ((Localization P.primeCompl) ⧸ IsLocalRing.maximalIdeal (Localization P.primeCompl)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  unfold LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength
  rw [(localizedPrimeResidueEquiv P).length_eq]
  exact Module.length_eq_one _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedPrimeFactor.BundleCycles
