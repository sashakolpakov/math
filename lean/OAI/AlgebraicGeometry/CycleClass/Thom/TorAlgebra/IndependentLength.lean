import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentChangeOfRings
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler

/-! # Independent Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentLength.Tor

noncomputable section

/-! Surjective change of rings preserves the exact native Tor lengths
and their truncated Euler sum when the second module is Tor-independent
of the quotient algebra. Infinite-length conventions are preserved too. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentChangeOfRings.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor

set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

local instance (M : ModuleCat.{u} S) :
    IsScalarTower R S ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

theorem length_restrictScalars (M : ModuleCat.{u} S) (hs : Function.Surjective (algebraMap R S)) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) = Module.length S M :=
  Module.length_eq_of_surjective (R := S) (S := R)
    (M := (ModuleCat.restrictScalars (algebraMap R S)).obj M) hs

variable (M : ModuleCat.{u} S) (N : ModuleCat.{u} R)
  (hs : Function.Surjective (algebraMap R S))
  (hv : ∀ n, IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R S)).obj N))

include hs hv

theorem tor_length (n : ℕ) :
    Module.length S (((Tor (ModuleCat S) n).obj M).obj ((FlatExtension.baseChange R S).obj N)) =
    Module.length R (((Tor (ModuleCat R) n).obj
      ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).obj N) :=
  (length_restrictScalars R S _ hs).symm.trans (IndependentChangeOfRings.Tor.torIso R S M N hv n).toLinearEquiv.length_eq

theorem euler_eq (d : ℕ) :
    Euler.Tor.euler S M ((FlatExtension.baseChange R S).obj N) d =
    Euler.Tor.euler R ((ModuleCat.restrictScalars (algebraMap R S)).obj M) N d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ)) (tor_length R S M N hs hv n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentLength.Tor
