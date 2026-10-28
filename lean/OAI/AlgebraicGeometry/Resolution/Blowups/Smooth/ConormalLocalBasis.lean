import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ConormalProjective
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedModuleFreeTransport
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Conormal Local Basis -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalLocalBasis.Construction

noncomputable section

/-! Every point of a smooth closed center has an actual principal neighborhood with a free conormal module. -/

theorem exists_smooth_center_conormal_free_neighborhood
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [Algebra.FormallySmooth k R] [IsNoetherianRing R]
    (I : Ideal R) [Algebra.FormallySmooth k (R ⧸ I)]
    (p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    ∃ r ∉ p, Module.Free
      (Localization.Away r ⧸ I.map (algebraMap R (Localization.Away r)))
      (I.map (algebraMap R (Localization.Away r))).Cotangent := by
  let Q := R ⧸ I
  let : Module.Finite Q I.Cotangent := Blowups.Quotient.ConormalProjective.Construction.smooth_quotient_conormal_finite I
  let : Module.Projective Q I.Cotangent := Blowups.Quotient.ConormalProjective.Construction.smooth_quotient_conormal_projective (k := k) I
  let : Module.FinitePresentation Q I.Cotangent := Module.finitePresentation_of_projective Q I.Cotangent
  let q : Ideal Q := p.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
  have hqfree : (⟨q, inferInstance⟩ : PrimeSpectrum Q) ∈ Module.freeLocus Q I.Cotangent := by
    rw [Module.freeLocus_eq_univ]
    trivial
  let : Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl I.Cotangent) := hqfree
  obtain ⟨s, hs, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl I.Cotangent) (Localization.AtPrime q)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
  have hr : r ∉ p := by
    intro hr
    exact hs (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hr)
  let S := Localization.Away r
  let Q' := S ⧸ I.map (algebraMap R S)
  let : IsLocalization.Away (Ideal.Quotient.mk I r) Q' :=
    Blowups.Quotient.LocalizedConormal.Construction.quotient_extended_ideal_isLocalizationAway r I
  let : Module Q (I.map (algebraMap R S)).Cotangent := Blowups.Quotient.LocalizedConormal.Construction.extendedCotangentQuotientModule I
  let : IsScalarTower Q Q' (I.map (algebraMap R S)).Cotangent := Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap_scalarTower I
  let F := Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap (S := S) I
  let : IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I r)) F :=
    Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap_isLocalizedModule r I
  let : Module.Free (Localization.Away (Ideal.Quotient.mk I r))
      (LocalizedModule.Away (Ideal.Quotient.mk I r) I.Cotangent) := hfree
  exact ⟨r, hr, LocalizedModuleFreeTransport.Construction.free_of_actual_localization (Submonoid.powers (Ideal.Quotient.mk I r)) F⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalLocalBasis.Construction
