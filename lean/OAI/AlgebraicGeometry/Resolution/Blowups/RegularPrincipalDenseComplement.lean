import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Localization
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupKernelSheaf

/-! # Regular Principal Dense Complement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.RegularPrincipalDenseComplement.Construction

noncomputable section

/-! Regular principal affine centers have a dense complement, including on disconnected reduced charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem regular_basicOpen_dense {R : Type} [CommRing R] (r : R) (hr : IsRegular r) :
    Dense (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
  have hi : Function.Injective (algebraMap R (Localization.Away r)) := by
    apply (IsLocalization.injective_iff_isRegular (M := Submonoid.powers r)).mpr
    rintro ⟨s, n, rfl⟩
    exact hr.pow n
  have hd : DenseRange (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]
    exact bot_le
  have he := congrArg (fun U : (Spec (.of R)).Opens => (U : Set (Spec (.of R))))
    (Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) r)
  change (Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))) =
    (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) at he
  exact he ▸ hd

theorem regular_affineQuotientKernel_supportComplement_dense
    {R : Type} [CommRing R] (r : R) (hr : IsRegular r) :
    Dense ((Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {r})).support.compl : Set (Spec (.of R))) := by
  have he : ((Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {r})).support.compl : Set (Spec (.of R))) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    have h := congrArg (fun s : Set (Spec (.of R)) => sᶜ) (Coefficient.ChartSupport.Construction.affineQuotientKernel_support (Ideal.span {r}))
    refine h.trans ?_
    ext p
    change ¬ Ideal.span {r} ≤ p.asIdeal ↔ r ∉ p.asIdeal
    rw [Ideal.span_singleton_le_iff_mem]
  exact he.symm ▸ regular_basicOpen_dense r hr

end

end OAI.AlgebraicGeometry.Resolution.Blowups.RegularPrincipalDenseComplement.Construction
