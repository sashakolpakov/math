import Mathlib.Algebra.Module.LocalizedModule.Away

/-! # Localization Fixed Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizationFixedClass

noncomputable section

/-! Localization detects equality of classes fixed by the localizing
function. This is the precise injectivity needed for a selected component. -/
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  (r : R)

theorem pow_fixed (x : M) (hx : r • x = x) (n : ℕ) : r^n • x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, hx, ih]

theorem eq_of_map_eq (f : M →ₗ[R] N) [IsLocalizedModule.Away r f]
    (x y : M) (hx : r • x = x) (hy : r • y = y) (h : f x = f y) : x = y := by
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r h
  simpa only [pow_fixed r x hx, pow_fixed r y hy] using hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizationFixedClass
