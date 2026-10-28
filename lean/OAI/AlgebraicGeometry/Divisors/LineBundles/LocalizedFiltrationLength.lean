import OAI.AlgebraicGeometry.Divisors.LineBundles.SubquotientImage
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Length

/-! # Localized Filtration Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: local lengths from actual prime filtrations

Localization carries the actual submodule exact sequence to an exact
sequence. Its module lengths therefore add, and the length of a localized
module is the sum of the lengths of its localized prime cyclic factors.
This statement uses extended natural lengths, so no finiteness is assumed.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

def LocalizedFiltrationLength.BundleCycles.localizedModuleEquiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
  IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) (Localization S) e

theorem LocalizedFiltrationLength.BundleCycles.localizedModuleLength_additive (P : Submodule R M) :
    Module.length (Localization S) (LocalizedModule S M) =
      Module.length (Localization S) (LocalizedModule S P) +
        Module.length (Localization S) (LocalizedModule S (M ⧸ P)) :=
  Module.length_eq_add_of_exact (LocalizedModule.map S P.subtype) (LocalizedModule.map S P.mkQ)
    (IsLocalizedModule.map_injective S _ _ P.subtype P.subtype_injective)
    (IsLocalizedModule.map_surjective S _ _ P.mkQ P.mkQ_surjective)
    (LocalizedModule.map_exact S P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P))

def LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength (J : Ideal R) : ℕ∞ :=
  Module.length (Localization S) (LocalizedModule S (R ⧸ J))

/-- All localized lengths are computed by the actual prime factors of the filtration. -/
theorem PrimeFiltration.BundleCycles.PrimeFiltrationAbove.localized_length_eq_sum {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) :
    Module.length (Localization S) (LocalizedModule S (M ⧸ N)) =
      (F.factors.map (LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength S)).sum := by
  induction F with
  | top => exact Module.length_eq_zero
  | step N L hNL J hJ e tail ih =>
    let P := L.map N.mkQ
    have he := (LocalizedFiltrationLength.BundleCycles.localizedModuleEquiv S ((SubquotientImage.BundleCycles.subquotientImageEquiv N L).symm.trans e)).length_eq
    have hq := (LocalizedFiltrationLength.BundleCycles.localizedModuleEquiv S
      (Submodule.quotientQuotientEquivQuotient N L hNL.le)).length_eq
    change _ = LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength S J + (tail.factors.map _).sum
    rw [LocalizedFiltrationLength.BundleCycles.localizedModuleLength_additive S P, he, hq, ih]
    rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
