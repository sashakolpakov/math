import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Factorial
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Etale.Basic

/-! # Etale Local -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.EtaleLocal.Construction.EtaleLocalFactorial

/-!
# Factorial local rings from étale coordinates

A residue-compatible map from a local essentially étale algebra into a
complete local factorial ring lifts uniquely enough for the descent argument:
formal smoothness supplies a lift, and unramifiedness makes it flat.
-/

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra.FormallyEtale R S] [Algebra.EssFiniteType R S]
variable [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalRing T] [IsDomain T] [UniqueFactorizationMonoid T] [Module.Flat R T]
variable [IsAdicComplete (IsLocalRing.maximalIdeal T) T]

theorem of_residue_map (q : S →ₐ[R] T ⧸ IsLocalRing.maximalIdeal T)
    (hq : RingHom.ker q = IsLocalRing.maximalIdeal S) : UniqueFactorizationMonoid S := by
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete q
  have hlocal : IsLocalHom g.toRingHom := by
    constructor
    intro s hs
    by_contra hn
    have hm : s ∈ IsLocalRing.maximalIdeal S := hn
    have hq0 : q s = 0 := by
      change s ∈ RingHom.ker q
      rwa [hq]
    have hg0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal T) (g s) = 0 :=
      (AlgHom.congr_fun hg s).trans hq0
    have hgm : g s ∈ IsLocalRing.maximalIdeal T := Ideal.Quotient.eq_zero_iff_mem.mp hg0
    exact hgm hs
  let : Algebra S T := g.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  have : Module.Flat S T := Algebra.FormallyUnramified.flat_of_restrictScalars R S T
  have : IsLocalHom (algebraMap S T) := hlocal
  have : Module.FaithfullyFlat S T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsDomain S := (FaithfulSMul.algebraMap_injective S T).isDomain (algebraMap S T)
  exact Factorial.Construction.FactorialDescent.of_faithfullyFlat (S := T)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.EtaleLocal.Construction.EtaleLocalFactorial
