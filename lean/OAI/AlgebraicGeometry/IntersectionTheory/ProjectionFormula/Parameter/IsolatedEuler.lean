import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.EulerSpecialization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FiberFiniteness
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.PrimeEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTransport

/-! # Isolated Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.IsolatedEuler

noncomputable section

/-! The specialization identity for an isolated parameter fiber,
with all Tor finiteness derived from the actual support condition. -/

open _root_.CategoryTheory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (r : R)
  (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]

theorem euler (hregular : IsSMulRegular R r)
    (hM : IsSMulRegular M r) (hN : IsSMulRegular N r)
    (d : ℕ) [HasProjectiveDimensionLE N d] (p₀ : PrimeSpectrum R)
    (hisolated : (Module.support R M ∩ Module.support R N) ∩
      Module.support R (ScalarQuotient.Ring R r) ⊆ {p₀}) :
    ProjectionFormula.Tor.Euler.euler (ScalarQuotient.Ring R r) ((ScalarQuotient.quotient R r).obj M) ((ScalarQuotient.quotient R r).obj N) d =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
        ProjectionFormula.Tor.Euler.euler R (((Tor (ModuleCat R) i).obj M).obj N)
          (.of R (ScalarQuotient.Ring R r)) 1 := by
  rw [EulerSpecialization.euler R r hregular M N hM hN d
    (FiberFiniteness.length_ne_top R r M N p₀ hisolated)]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a : ℚ => (-1 : ℚ) ^ i * a)
    (ProjectionFormula.Tor.EulerTransport.iso_right R _
      (PrimeEuler.quotientEquiv R r).symm.toModuleIso 1)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.IsolatedEuler
