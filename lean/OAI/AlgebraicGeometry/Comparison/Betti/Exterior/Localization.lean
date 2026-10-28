import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.BaseChange
import Mathlib.RingTheory.Etale.Kaehler

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Localization

noncomputable section

/-! Actual exterior differential forms localize on charts where the differential module is free. -/

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

def coefficientExteriorMap (n : ℕ) : ⋀[A]^n Ω[A⁄R] →ₗ[A] ⋀[B]^n Ω[B⁄R] :=
  BaseChange.map (S := B) (KaehlerDifferential.map R R A B) n

theorem coefficientExteriorMap_mk (n : ℕ) (v : Fin n → Ω[A⁄R]) :
    coefficientExteriorMap R A B n (exteriorPower.ιMulti A n v) =
      exteriorPower.ιMulti B n (fun i => KaehlerDifferential.map R R A B (v i)) :=
  BaseChange.map_mk _ n v

theorem coefficientExteriorMap_isBaseChange [Algebra.FormallyEtale A B]
    [Module.Free A Ω[A⁄R]] (n : ℕ) : IsBaseChange B (coefficientExteriorMap R A B n) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex A Ω[A⁄R]) := linearOrderOfSTO WellOrderingRel
  exact BaseChange.isBaseChange (KaehlerDifferential.map R R A B)
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B)
    (Module.Free.chooseBasis A Ω[A⁄R]) n

theorem coefficientExteriorMap_isLocalizedModule (S : Submonoid A) [IsLocalization S B]
    [Module.Free A Ω[A⁄R]] (n : ℕ) : IsLocalizedModule S (coefficientExteriorMap R A B n) := by
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  exact (isLocalizedModule_iff_isBaseChange S B _).mpr
    (coefficientExteriorMap_isBaseChange R A B n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Localization
