import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Localization Range -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationRange.LocalizationRangeDescent

noncomputable section

/-!
# Descent of module images from principal localizations

For coefficients generating the unit ideal, membership in the image of a
linear map can be checked after localizing source and target at each
coefficient. Denominator clearing gives a power multiple in the original
image; the unit-ideal criterion then gives the original membership.
-/

universe u

variable (R ι M N : Type u) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (s : ι → R)
  (ML NL : ι → Type u) [∀ i, AddCommGroup (ML i)] [∀ i, Module R (ML i)]
  [∀ i, AddCommGroup (NL i)] [∀ i, Module R (NL i)]
  (m : ∀ i, M →ₗ[R] ML i) (n : ∀ i, N →ₗ[R] NL i)
  [∀ i, IsLocalizedModule (Submonoid.powers (s i)) (m i)]
  [∀ i, IsLocalizedModule (Submonoid.powers (s i)) (n i)]
  (fl : ∀ i, ML i →ₗ[R] NL i)
  (commute : ∀ i x, n i (f x) = fl i (m i x))

include commute in
theorem power_smul_mem (i : ι) (x : N) (hx : n i x ∈ LinearMap.range (fl i)) :
    ∃ e : ℕ, (s i) ^ e • x ∈ LinearMap.range f := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨⟨z, t⟩, ht⟩ := IsLocalizedModule.surj (Submonoid.powers (s i)) (m i) y
  have he : n i (f z) = n i ((t : R) • x) := by
    rw [commute, ← ht]
    change fl i ((t : R) • y) = n i ((t : R) • x)
    rw [map_smul, hy, map_smul]
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (s i)) (f := n i) he
  obtain ⟨a, ha⟩ := t.property
  obtain ⟨b, hb⟩ := v.property
  have hp : (v : R) * (t : R) = s i ^ (b + a) := by rw [← hb, ← ha, pow_add]
  refine ⟨b + a, ⟨(v : R) • z, ?_⟩⟩
  change (v : R) • f z = (v : R) • ((t : R) • x) at hv
  exact ((f.map_smul (v : R) z).trans hv).trans (by rw [← mul_smul, hp])

include commute in
theorem mem_range (hs : Ideal.span (Set.range s) = ⊤) (x : N)
    (hx : ∀ i, n i x ∈ LinearMap.range (fl i)) : x ∈ LinearMap.range f := by
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range f) (Set.range s) hs x
  intro r
  obtain ⟨i, hi⟩ := r.property
  obtain ⟨e, he⟩ := power_smul_mem R ι M N f s ML NL m n fl commute i x (hx i)
  exact ⟨e, hi ▸ he⟩

include commute in
theorem mem_range_iff (hs : Ideal.span (Set.range s) = ⊤) (x : N) :
    x ∈ LinearMap.range f ↔ ∀ i, n i x ∈ LinearMap.range (fl i) := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨m i y, (commute i y).symm⟩
  · exact mem_range R ι M N f s ML NL m n fl commute hs x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationRange.LocalizationRangeDescent
