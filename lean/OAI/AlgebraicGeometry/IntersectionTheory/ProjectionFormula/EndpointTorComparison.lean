import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientScalars
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RingEquivTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler

/-! # Endpoint Tor Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EndpointTorComparison

noncomputable section

/-! Native Tor over the parameter quotient has the actual endpoint
Tor lengths when both quotient modules are identified with their
endpoint modules through the native ambient quotient map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

variable (R S : Type u) [CommRing R] [CommRing S] (r : R) (φ : R →+* S)
  (hφ : Function.Surjective φ) (hk : RingHom.ker φ = Ideal.span {r})
  (M N : ModuleCat.{u} R) (M₀ N₀ : ModuleCat.{u} S)
  (eM : QuotSMulTop r M ≃ₗ[R] (ModuleCat.restrictScalars φ).obj M₀)
  (eN : QuotSMulTop r N ≃ₗ[R] (ModuleCat.restrictScalars φ).obj N₀)

include hφ hk eM eN

theorem length (n : ℕ) :
    Module.length (Parameter.ScalarQuotient.Ring R r)
      (((Tor (ModuleCat (Parameter.ScalarQuotient.Ring R r)) n).obj
        ((Parameter.ScalarQuotient.quotient R r).obj M)).obj
        ((Parameter.ScalarQuotient.quotient R r).obj N)) =
      Module.length S (((Tor (ModuleCat S) n).obj M₀).obj N₀) := by
  let Q := Parameter.ScalarQuotient.Ring R r
  let σ := Principal.QuotientScalars.ringEquiv R S r φ hk hφ
  let eM' := Principal.QuotientScalars.extendEquiv R S r φ hk M M₀ eM
  let eN' := Principal.QuotientScalars.extendEquiv R S r φ hk N N₀ eN
  exact (Open.SupportTor.length_iso Q eM'.toModuleIso eN'.toModuleIso n).trans
    (RingEquivTor.length σ M₀ N₀ n)

theorem euler (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler (Parameter.ScalarQuotient.Ring R r)
      ((Parameter.ScalarQuotient.quotient R r).obj M)
      ((Parameter.ScalarQuotient.quotient R r).obj N) d =
      ProjectionFormula.Tor.Euler.euler S M₀ N₀ d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ))
    (EndpointTorComparison.length R S r φ hφ hk M N M₀ N₀ eM eN n)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EndpointTorComparison
