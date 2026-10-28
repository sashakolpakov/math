import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExcessSequenceLeftBound
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.QuotientProjectiveDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerCutoff
import Mathlib.RingTheory.KrullDimension.Module

/-! # Zero Dimensional Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ZeroDimensionalEuler

noncomputable section

/-! A nonempty regular sequence has zero native Tor Euler characteristic
against a finite module of support dimension zero, even over a singular
Noetherian local ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence
open scoped Pointwise

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (N : ModuleCat.{u} R) [Module.Finite R N]
  (rs : List R) (hr : IsWeaklyRegular R rs) (hne : rs ≠ [])
  (hm : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
  (hd : Module.supportDim R N = 0)

include hr hne hm hd

theorem euler_eq_zero : Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N rs.length = 0 := by
  have hi : (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs := by
    change Ideal.ofList rs * ⊤ = Ideal.ofList rs
    exact Ideal.mul_top _
  let : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R))) rs.length := by
    rw [hi]
    exact Regular.QuotientProjectiveDimension.Constructions.bound R rs hr hm
  have hN : Module.support R N ⊆ {IsLocalRing.closedPoint R} := by
    rw [support_of_supportDim_eq_zero R N hd, PrimeSpectrum.zeroLocus_eq_singleton]
    exact le_rfl
  have h := ExcessSequenceLeftBound.euler_sequence_eq_zero R N rs.length
    (ModuleCat.of R R) rs hr hne (IsLocalRing.closedPoint R) (Set.inter_subset_right.trans hN)
  change Euler.Tor.euler R (ModuleCat.of R (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R))) N rs.length = 0 at h
  rw [hi] at h
  exact h

theorem euler_eq_zero_above_length (d : ℕ) (hD : rs.length ≤ d) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N d = 0 := by
  let := Regular.QuotientProjectiveDimension.Constructions.bound R rs hr hm
  exact (EulerCutoff.stable_left R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N
    rs.length d hD).trans (euler_eq_zero R N rs hr hne hm hd)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ZeroDimensionalEuler
