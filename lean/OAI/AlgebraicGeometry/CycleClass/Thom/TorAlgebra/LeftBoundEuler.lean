import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Symmetry
import Mathlib.RingTheory.Regular.Category

/-! # Left Bound Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LeftBoundEuler

noncomputable section

/-! Tor Euler additivity can use a projective-dimension bound on the
quotient in the first variable. The other input may have infinite
projective dimension, as occurs over singular intermediate quotient rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteLength.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BoundedResolution

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R]

theorem tor_isZero_left (M N : ModuleCat.{u} R) (d n : ℕ)
    [HasProjectiveDimensionLE M d] (hn : d < n) :
    IsZero (((Tor (ModuleCat R) n).obj M).obj N) :=
  (BoundedResolution.tor_isZero R N M d n hn).of_iso (Symmetry.Tor.iso R M N n)

variable [IsNoetherianRing R] (N : ModuleCat.{u} R) [Module.Finite R N] (d : ℕ)

theorem additivity (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
    [HasProjectiveDimensionLE S.X₃ d]
    (x : PrimeSpectrum R) (hx : Module.support R S.X₂ ∩ Module.support R N ⊆ {x}) :
    Euler.Tor.euler R S.X₂ N d = Euler.Tor.euler R S.X₁ N d + Euler.Tor.euler R S.X₃ N d := by
  have h₁ : Module.support R S.X₁ ∩ Module.support R N ⊆ {x} :=
    (Set.inter_subset_inter_left _ (Module.support_subset_of_injective S.f.hom hS.moduleCat_injective_f)).trans hx
  have h₃ : Module.support R S.X₃ ∩ Module.support R N ⊆ {x} :=
    (Set.inter_subset_inter_left _ (Module.support_subset_of_surjective S.g.hom hS.moduleCat_surjective_g)).trans hx
  exact Euler.Tor.additivity R N S hS d (FiniteLength.Tor.tor_length_ne_top R S.X₁ N x h₁)
    (FiniteLength.Tor.tor_length_ne_top R S.X₂ N x hx) (FiniteLength.Tor.tor_length_ne_top R S.X₃ N x h₃)
    (tor_isZero_left R S.X₃ N d (d + 1) (Nat.lt_succ_self d))

theorem euler_quotient_eq_zero (M : ModuleCat.{u} R) [Module.Finite R M]
    (r : R) (hr : IsSMulRegular M r)
    [HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop r M)) d]
    (x : PrimeSpectrum R) (hx : Module.support R M ∩ Module.support R N ⊆ {x}) :
    Euler.Tor.euler R (ModuleCat.of R (QuotSMulTop r M)) N d = 0 := by
  let S := M.smulShortComplex r
  let : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R M)
  let : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R M)
  let : Module.Finite R S.X₃ := inferInstanceAs (Module.Finite R (QuotSMulTop r M))
  let : HasProjectiveDimensionLE S.X₃ d :=
    inferInstanceAs (HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop r M)) d)
  have h := additivity R N d S (IsSMulRegular.smulShortComplex_shortExact hr) x hx
  change Euler.Tor.euler R M N d = Euler.Tor.euler R M N d + Euler.Tor.euler R (ModuleCat.of R (QuotSMulTop r M)) N d at h
  exact add_left_cancel (h.symm.trans (add_zero (Euler.Tor.euler R M N d)).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LeftBoundEuler
