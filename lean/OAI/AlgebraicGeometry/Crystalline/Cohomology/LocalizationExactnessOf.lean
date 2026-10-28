import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationRange
import Mathlib.Algebra.Exact.Basic

/-! # Localization Exactness Of -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationExactnessOf.LocalizationExactness

noncomputable section

/-!
# Exactness descends from principal-localized module complexes

For a unit-ideal family of coefficients, a pair of module maps is exact
if its localized pairs are exact. Only the incoming and middle modules
need localization hypotheses; commutation with the outgoing map carries
each original cocycle to a localized cocycle.
-/

universe u

variable (R ι M N P : Type u) [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) (s : ι → R)
  (ML NL PL : ι → Type u)
  [∀ i, AddCommGroup (ML i)] [∀ i, Module R (ML i)]
  [∀ i, AddCommGroup (NL i)] [∀ i, Module R (NL i)]
  [∀ i, AddCommGroup (PL i)] [∀ i, Module R (PL i)]
  (m : ∀ i, M →ₗ[R] ML i) (n : ∀ i, N →ₗ[R] NL i) (o : ∀ i, P →ₗ[R] PL i)
  [∀ i, IsLocalizedModule (Submonoid.powers (s i)) (m i)]
  [∀ i, IsLocalizedModule (Submonoid.powers (s i)) (n i)]
  (fl : ∀ i, ML i →ₗ[R] NL i) (gl : ∀ i, NL i →ₗ[R] PL i)
  (commute_f : ∀ i x, n i (f x) = fl i (m i x))
  (commute_g : ∀ i x, gl i (n i x) = o i (g x))

include hgf commute_f commute_g in
theorem exact_of_localized (hs : Ideal.span (Set.range s) = ⊤)
    (hl : ∀ i, Function.Exact (fl i) (gl i)) : Function.Exact f g := by
  intro x
  constructor
  · intro hx
    apply LocalizationRange.LocalizationRangeDescent.mem_range R ι M N f s ML NL m n fl commute_f hs x
    intro i
    apply (hl i (n i x)).mp
    rw [commute_g, hx, map_zero]
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hgf y

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationExactnessOf.LocalizationExactness
