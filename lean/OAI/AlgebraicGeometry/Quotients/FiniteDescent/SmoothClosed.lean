import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothLocal
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-! # Smooth Closed -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothClosed.Construction.SmoothClosedFactorial

noncomputable section

/-! All prime local rings of a smooth algebra over an algebraically closed field are factorial. -/

variable {K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Algebra K S]
variable [Algebra.Smooth K S]

include K

theorem at_maximal (m : Ideal S) [m.IsMaximal] :
    UniqueFactorizationMonoid (Localization.AtPrime m) := by
  let := Ideal.Quotient.field m
  have : Module.Finite K (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ m)
  let e : K ≃ₐ[K] S ⧸ m := AlgEquiv.ofBijective (Algebra.ofId K (S ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let q : S →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m)
  have hq : RingHom.ker q = m := by
    ext s
    change e.symm (Ideal.Quotient.mk m s) = 0 ↔ s ∈ m
    rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hs : (RingHom.ker q).primeCompl = m.primeCompl := by
    ext s
    change s ∉ RingHom.ker q ↔ s ∉ m
    rw [hq]
  have : IsLocalization (RingHom.ker q).primeCompl (Localization.AtPrime m) := by
    rw [hs]
    infer_instance
  have : UniqueFactorizationMonoid (Localization.AtPrime (RingHom.ker q)) :=
    SmoothLocal.Construction.SmoothLocalFactorial.at_rational_point q
  let eqv := IsLocalization.algEquiv (RingHom.ker q).primeCompl
    (Localization.AtPrime (RingHom.ker q)) (Localization.AtPrime m)
  exact eqv.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance

theorem at_prime (p : Ideal S) [p.IsPrime] :
    UniqueFactorizationMonoid (Localization.AtPrime p) := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p ‹p.IsPrime›.ne_top
  have : m.IsMaximal := hm
  have : UniqueFactorizationMonoid (Localization.AtPrime m) := at_maximal (K := K) m
  let A := Localization.AtPrime m
  let B := Localization.AtPrime p
  have hle : m.primeCompl ≤ p.primeCompl := fun x hx => fun hxp => hx (hpm hxp)
  let : Algebra A B := IsLocalization.localizationAlgebraOfSubmonoidLe
    A B m.primeCompl p.primeCompl hle
  have : IsScalarTower S A B := IsLocalization.localization_isScalarTower_of_submonoid_le
    A B m.primeCompl p.primeCompl hle
  have : IsLocalization (p.primeCompl.map (algebraMap S A)) B :=
    IsLocalization.isLocalization_of_submonoid_le A B m.primeCompl p.primeCompl hle
  exact UniqueFactorizationMonoid.of_isLocalization (p.primeCompl.map (algebraMap S A)) B

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothClosed.Construction.SmoothClosedFactorial
