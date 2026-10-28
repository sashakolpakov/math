import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps
import OAI.AlgebraicGeometry.Divisors.LineBundles.InfinitesimalCoordinates

/-! # Cone Injection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeInjection.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual normal-cone injectivity from infinitesimal coordinate lifts -/

variable {R S : Type} [CommRing R] [CommRing S]

theorem normalConeMap_injective_of_power_comap (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I ≤ J.comap f) (hpow : ∀ n, (J ^ n).comap f = I ^ n) :
    Function.Injective (Deformation.Maps.BundleCycles.normalConeMap I J f hf) := by
  apply (injective_iff_map_eq_zero (Deformation.Maps.BundleCycles.normalConeMap I J f hf)).mpr
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff I p).mpr
  have hp : Deformation.Maps.BundleCycles.reesMap I J f hf p ∈ Cone.BundleCycles.normalConeIdeal J := Ideal.Quotient.eq_zero_iff_mem.mp ha
  intro n
  have hn := (ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff J _).mp hp n
  rw [Deformation.Maps.BundleCycles.reesMap_coeff] at hn
  have hn' : p.val.coeff n ∈ (J ^ (n + 1)).comap f := hn
  exact (hpow (n + 1)) ▸ hn'

theorem formallySmooth_normalConeMap_injective [Algebra R S] [Algebra.FormallySmooth R S]
    (I : Ideal R) (q : S →ₐ[R] R ⧸ I) :
    Function.Injective (Deformation.Maps.BundleCycles.normalConeMap I (RingHom.ker q) (algebraMap R S)
      (fun r hr => (q.commutes r).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hr))) :=
  normalConeMap_injective_of_power_comap I (RingHom.ker q) (algebraMap R S) _
    (InfinitesimalCoordinates.BundleCycles.formallySmooth_ker_power_comap I q)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeInjection.BundleCycles
