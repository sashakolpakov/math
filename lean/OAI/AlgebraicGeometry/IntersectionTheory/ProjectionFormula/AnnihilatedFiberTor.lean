import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.ParameterTorReduction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EndpointTorComparison

/-! # Annihilated Fiber Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AnnihilatedFiberTor

noncomputable section

/-! If the first module already lies on a regular parameter fiber,
its pairing with a parameter-regular second module is computed by the
native fiber Tor. The comparison holds in every Tor degree. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

variable (R S : Type u) [CommRing R] [CommRing S] (r : R) (hr : IsSMulRegular R r)
  (φ : R →+* S) (hφ : Function.Surjective φ) (hk : RingHom.ker φ = Ideal.span {r})
  (M N : ModuleCat.{u} R) (hM : ∀ m : M, r • m = 0) (hN : IsSMulRegular N r)
  (M₀ N₀ : ModuleCat.{u} S)
  (eM : QuotSMulTop r M ≃ₗ[R] (ModuleCat.restrictScalars φ).obj M₀)
  (eN : QuotSMulTop r N ≃ₗ[R] (ModuleCat.restrictScalars φ).obj N₀)

include hr hφ hk hM hN eM eN

theorem length (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj M).obj N) =
      Module.length S (((Tor (ModuleCat S) n).obj M₀).obj N₀) :=
  (Regular.ParameterTorReduction.length R r hr M N hM hN n).symm.trans
    (EndpointTorComparison.length R S r φ hφ hk M N M₀ N₀ eM eN n)

theorem euler (d : ℕ) : ProjectionFormula.Tor.Euler.euler R M N d = ProjectionFormula.Tor.Euler.euler S M₀ N₀ d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ))
    (AnnihilatedFiberTor.length R S r hr φ hφ hk M N hM hN M₀ N₀ eM eN n)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AnnihilatedFiberTor
