import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength

/-! # Localized Tor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedTorEuler

noncomputable section

/-! Localized native module lengths give exactly the native Tor
Euler characteristic after flat localization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R]

theorem length_zero (M : ModuleCat.{u} R) (p : PrimeSpectrum R)
    (hp : p ∉ Module.support R M) :
    FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M = 0 := by
  let : Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := Module.notMem_support_iff.mp hp
  let : Subsingleton (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm.injective.subsingleton
  exact Module.length_eq_zero

theorem euler (M N : ModuleCat.{u} R) (p : PrimeSpectrum R) (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler (Localization.AtPrime p.asIdeal)
      ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj M)
      ((Flat.Extension.baseChange R (Localization.AtPrime p.asIdeal)).obj N) d =
    ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal)
        (((Tor (ModuleCat R) i).obj M).obj N)).toNat : ℚ) := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ i * (a.toNat : ℚ))
    (Flat.Extension.torBaseChangeIso R (Localization.AtPrime p.asIdeal) M N i).toLinearEquiv.length_eq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedTorEuler
