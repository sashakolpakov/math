import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentPowerLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Power Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PowerLift

noncomputable section

/-! Canonical lifts of powered units on the actual affine sections of
a closed reduction modulo p. They commute with affine restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (p : ℕ) [Fact p.Prime] (n : ℕ)
  {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
  (hn : ∀ U : X.Opens, (p : Γ(X, U)) ^ (n + 1) = 0)
  (hker : ∀ (U : X.Opens) (_hU : IsAffineOpen U),
    RingHom.ker (f.app U).hom = Ideal.span {(p : Γ(X, U))})

def units (U : X.Opens) (hU : IsAffineOpen U) : Γ(Y, f ⁻¹ᵁ U)ˣ →* Γ(X, U)ˣ :=
  NilpotentPowerLift.units p n (hn U) (f.app U).hom (f.app_surjective U hU) (hker U hU)

theorem units_reduction (U : X.Opens) (hU : IsAffineOpen U) (a : Γ(Y, f ⁻¹ᵁ U)ˣ) :
    Units.map (f.app U).hom.toMonoidHom (units p n f hn hker U hU a) = a ^ (p ^ n) :=
  NilpotentPowerLift.units_reduction p n (hn U) (f.app U).hom
    (f.app_surjective U hU) (hker U hU) a

theorem units_restriction (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) (a : Γ(Y, f ⁻¹ᵁ U)ˣ) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
      (units p n f hn hker U hU a) =
    units p n f hn hker V hV
      (Units.map (Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map (homOfLE h)).op).hom.toMonoidHom a) := by
  apply NilpotentPowerLift.units_naturality
  apply RingHom.ext
  intro x
  exact ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PowerLift
