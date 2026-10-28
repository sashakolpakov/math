import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Ideal.Maps

/-! # Surjective Localization Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurjectiveLocalizationKernel.BundleCycles

/-! The kernel of the actual localized map of a surjective ring
homomorphism is the extension of the original kernel. -/

theorem surjectiveLocalization_kernel
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [IsLocalization p.primeCompl A] [IsLocalization q.primeCompl B]
    (g : R →+* S) (hg : Function.Surjective g) (hpq : q.comap g = p)
    (φ : A →+* B) (hφ : φ.comp (algebraMap R A) = (algebraMap S B).comp g) :
    RingHom.ker φ = (RingHom.ker g).map (algebraMap R A) := by
  subst p
  have hT : Submonoid.map g (q.comap g).primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective g hg q
  have hφ' : φ = IsLocalization.map B g (hT.symm ▸ (q.comap g).primeCompl.le_comap_map) :=
    IsLocalization.ringHom_ext (q.comap g).primeCompl (hφ.trans (IsLocalization.map_comp _).symm)
  rw [hφ']
  exact IsLocalization.ker_map B g hT

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurjectiveLocalizationKernel.BundleCycles
