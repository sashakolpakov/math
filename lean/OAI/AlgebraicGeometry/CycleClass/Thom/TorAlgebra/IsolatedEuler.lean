import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteLength

/-! # Isolated Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler

noncomputable section

/-! Additivity of the actual Tor Euler characteristic at an isolated
support intersection. Its finite-length and truncation requirements
follow from module support and a genuine projective-dimension bound. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteLength.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BoundedResolution

universe u
variable (R : Type u) [CommRing R]

theorem euler_iso_left {M M' : ModuleCat.{u} R} (e : M ≅ M')
    (N : ModuleCat.{u} R) (d : ℕ) : Euler.Tor.euler R M N d = Euler.Tor.euler R M' N d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ))
    ((((Tor (ModuleCat R) n).mapIso e).app N).toLinearEquiv.length_eq)

theorem euler_subsingleton_left (M N : ModuleCat.{u} R) [Subsingleton M] (d : ℕ) :
    Euler.Tor.euler R M N d = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  let := Support.Tor.subsingleton_left R M N n
  simp only [ExactLength.rationalLength, Module.length_eq_zero,
    ENat.toNat_zero, Nat.cast_zero, mul_zero]

variable [IsNoetherianRing R] (N : ModuleCat.{u} R) [Module.Finite R N]
  (d : ℕ) [HasProjectiveDimensionLE N d]

theorem additivity_of_isolated_support (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    (x : PrimeSpectrum R) (hx : Module.support R S.X₂ ∩ Module.support R N ⊆ {x}) :
    Euler.Tor.euler R S.X₂ N d = Euler.Tor.euler R S.X₁ N d + Euler.Tor.euler R S.X₃ N d := by
  have h₁ : Module.support R S.X₁ ∩ Module.support R N ⊆ {x} :=
    (Set.inter_subset_inter_left _ (Module.support_subset_of_injective S.f.hom hS.moduleCat_injective_f)).trans hx
  have h₃ : Module.support R S.X₃ ∩ Module.support R N ⊆ {x} :=
    (Set.inter_subset_inter_left _ (Module.support_subset_of_surjective S.g.hom hS.moduleCat_surjective_g)).trans hx
  exact Euler.Tor.additivity R N S hS d (FiniteLength.Tor.tor_length_ne_top R S.X₁ N x h₁)
    (FiniteLength.Tor.tor_length_ne_top R S.X₂ N x hx) (FiniteLength.Tor.tor_length_ne_top R S.X₃ N x h₃)
    (BoundedResolution.tor_isZero R S.X₃ N d (d + 1) (Nat.lt_succ_self d))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler
