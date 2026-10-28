import Mathlib.LinearAlgebra.BilinearMap

/-! # Bilinear Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearRestriction

noncomputable section

/-! Restriction of a bilinear map along an explicit ring homomorphism,
with the existing module actions retained. -/

variable (R S : Type*) [CommRing R] [CommRing S] (φ : S →+* R)
  (M N P : Type*) [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  [Module S M] [Module S N] [Module S P]
  (hM : ∀ s (x : M), s • x = φ s • x)
  (hN : ∀ s (x : N), s • x = φ s • x)
  (hP : ∀ s (x : P), s • x = φ s • x)
  (b : M →ₗ[R] N →ₗ[R] P)

def map : M →ₗ[S] N →ₗ[S] P :=
  LinearMap.mk₂ S (fun x y => b x y)
    (fun x x' y => LinearMap.congr_fun (b.map_add x x') y)
    (fun s x y => by
      rw [hM, hP]
      exact LinearMap.congr_fun (b.map_smul (φ s) x) y)
    (fun x y y' => (b x).map_add y y')
    (fun s x y => by
      rw [hN, hP]
      exact (b x).map_smul (φ s) y)

theorem map_apply (x : M) (y : N) : map R S φ M N P hM hN hP b x y = b x y := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearRestriction
