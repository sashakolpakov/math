import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrimeEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ZeroDimensionalEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport

/-! # Regular Prime Devissage -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularPrimeDevissage

noncomputable section

/-! Reducing regular-sequence Euler vanishing to prime quotients
without imposing a projective-dimension bound on the source module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor

universe u
variable (R : Type u) [CommRing R]

theorem supportDim_le_of_support_subset (M N : ModuleCat.{u} R)
    (h : Module.support R M ⊆ Module.support R N) : Module.supportDim R M ≤ Module.supportDim R N :=
  Order.krullDim_le_of_strictMono (fun p => ⟨p.val, h p.property⟩)
    (fun {_ _} hlt => hlt)

theorem euler_eq_zero_of_supportDim_lt_zero (M N : ModuleCat.{u} R)
    (hd : Module.supportDim R N < 0) (d : ℕ) : Euler.Tor.euler R M N d = 0 := by
  let : Subsingleton N := (Module.supportDim_eq_bot_iff_subsingleton R N).mp
    ((WithBot.lt_zero_iff_eq_bot _).mp hd)
  exact (EulerTransport.Tor.comm R M N d).trans
    (IsolatedEuler.euler_subsingleton_left R N M d)

variable [IsNoetherianRing R] [IsLocalRing R]
  (N : ModuleCat.{u} R) [Module.Finite R N]
  (rs : List R) (hr : IsWeaklyRegular R rs)
  (hm : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)

include hr hm

theorem euler_eq_zero_of_supportDim_nonpos (hne : rs ≠ []) (hd : Module.supportDim R N ≤ 0) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N rs.length = 0 := by
  rcases lt_or_eq_of_le hd with hd | hd
  · exact euler_eq_zero_of_supportDim_lt_zero R _ N hd rs.length
  · exact ZeroDimensionalEuler.euler_eq_zero R N rs hr hne hm hd

theorem euler_eq_zero_of_prime_quotients
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩ Module.support R N ⊆
      {IsLocalRing.closedPoint R})
    (hz : ∀ p : PrimeSpectrum R, Module.support R (R ⧸ p.asIdeal) ⊆ Module.support R N →
      Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R (R ⧸ p.asIdeal)) rs.length = 0) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N rs.length = 0 := by
  let := Regular.QuotientProjectiveDimension.Constructions.bound R rs hr hm
  have hI : Module.support R (R ⧸ Ideal.ofList rs) =
      PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hN : Module.support R N ∩ Module.support R (R ⧸ Ideal.ofList rs) ⊆
      {IsLocalRing.closedPoint R} := by
    rw [hI, Set.inter_comm]
    exact hi
  obtain ⟨ps, hps, he⟩ := PrimeEuler.exists_prime_euler_sum R
    (ModuleCat.of R (R ⧸ Ideal.ofList rs)) rs.length N (IsLocalRing.closedPoint R) hN
  rw [EulerTransport.Tor.comm R _ N, he]
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact (EulerTransport.Tor.comm R _ _ rs.length).trans (hz p (hps p hp))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularPrimeDevissage
