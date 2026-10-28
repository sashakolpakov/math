import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization

/-! # Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Support

noncomputable section

/-! Localizing Tor uses the actual flat base-change isomorphism. Hence
its module support is contained in the intersection of the input supports. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

namespace Tor

universe u

variable (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)

theorem subsingleton_left [Subsingleton M] (n : ℕ) :
    Subsingleton (((Tor (ModuleCat R) n).obj M).obj N) := by
  let : Projective M := (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).projective
  let : Module.Projective R M := inferInstance
  cases n with
  | zero =>
    exact (TorAlgebra.Flat.Tor.torZeroIso R M N).toLinearEquiv.injective.subsingleton
  | succ n => exact ModuleCat.subsingleton_of_isZero (TorAlgebra.Flat.Tor.higherTor_isZero R M N n)

theorem subsingleton_right [Subsingleton N] (n : ℕ) :
    Subsingleton (((Tor (ModuleCat R) n).obj M).obj N) := by
  let : Projective N := (ModuleCat.isZero_iff_subsingleton.mpr inferInstance).projective
  cases n with
  | zero =>
    exact (TorAlgebra.Flat.Tor.torZeroIso R M N).toLinearEquiv.injective.subsingleton
  | succ n =>
    exact ModuleCat.subsingleton_of_isZero
      (isZero_Tor_succ_of_projective (ModuleCat R) M N n)

theorem notMem_support_of_left (n : ℕ) (p : PrimeSpectrum R)
    (hp : p ∉ Module.support R M) :
    p ∉ Module.support R (((Tor (ModuleCat R) n).obj M).obj N) := by
  have hM := Module.notMem_support_iff.mp hp
  let : Subsingleton ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj M) := by
    change Subsingleton (Localization.AtPrime p.asIdeal ⊗[R] M)
    exact (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm.injective.subsingleton
  let : Subsingleton (((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).obj
      ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj M)).obj
      ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj N)) :=
    subsingleton_left (Localization.AtPrime p.asIdeal) _ _ n
  let : Subsingleton (Localization.AtPrime p.asIdeal ⊗[R]
      (((Tor (ModuleCat R) n).obj M).obj N)) :=
    (FlatExtension.torBaseChangeIso R (Localization.AtPrime p.asIdeal) M N n).symm.toLinearEquiv.injective.subsingleton
  exact Module.notMem_support_iff.mpr
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl
      (((Tor (ModuleCat R) n).obj M).obj N)).injective.subsingleton

theorem notMem_support_of_right (n : ℕ) (p : PrimeSpectrum R)
    (hp : p ∉ Module.support R N) :
    p ∉ Module.support R (((Tor (ModuleCat R) n).obj M).obj N) := by
  have hN := Module.notMem_support_iff.mp hp
  let : Subsingleton ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj N) := by
    change Subsingleton (Localization.AtPrime p.asIdeal ⊗[R] N)
    exact (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N).symm.injective.subsingleton
  let : Subsingleton (((Tor (ModuleCat (Localization.AtPrime p.asIdeal)) n).obj
      ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj M)).obj
      ((FlatExtension.baseChange R (Localization.AtPrime p.asIdeal)).obj N)) :=
    subsingleton_right (Localization.AtPrime p.asIdeal) _ _ n
  let : Subsingleton (Localization.AtPrime p.asIdeal ⊗[R]
      (((Tor (ModuleCat R) n).obj M).obj N)) :=
    (FlatExtension.torBaseChangeIso R (Localization.AtPrime p.asIdeal) M N n).symm.toLinearEquiv.injective.subsingleton
  exact Module.notMem_support_iff.mpr
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl
      (((Tor (ModuleCat R) n).obj M).obj N)).injective.subsingleton

theorem support_subset (n : ℕ) :
    Module.support R (((Tor (ModuleCat R) n).obj M).obj N) ⊆
      Module.support R M ∩ Module.support R N := by
  intro p hp
  exact ⟨by_contra fun h => notMem_support_of_left R M N n p h hp,
    by_contra fun h => notMem_support_of_right R M N n p h hp⟩

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Support
