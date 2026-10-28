import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.FamilyCharts

/-! # Chart Support -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups

/-! Normal equations detect the native carrier on every actual coefficient chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Coefficient.ChartSupport.Construction.affineQuotientKernel_support {R : Type} [CommRing R] (I : Ideal R) :
    ((Affine.QuotientKernel.Construction.affineQuotientKernel I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus I := by
  rw [Affine.QuotientKernel.Construction.affineQuotientKernel, Scheme.Hom.support_ker]
  change closure (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  exact (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).closure_eq

theorem GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart.normal_mem_iff
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J H : X.IdealSheafData}
    {C : H.subscheme.IdealSheafData} {b : ℕ} (T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b)
    (q : PrimeSpectrum T.ring) : T.normal ∈ q.asIdeal ↔ T.map q ∈ H.support := by
  have he := congrArg (fun I : (Spec T.ring).IdealSheafData => (I.support : Set (Spec T.ring))) T.hypersurface
  rw [Scheme.IdealSheafData.support_comap, Coefficient.ChartSupport.Construction.affineQuotientKernel_support] at he
  change T.map ⁻¹' (H.support : Set X) = PrimeSpectrum.zeroLocus (Ideal.span {T.normal}) at he
  change T.normal ∈ q.asIdeal ↔ q ∈ T.map ⁻¹' (H.support : Set X)
  exact (Ideal.span_singleton_le_iff_mem (I := q.asIdeal)).symm.trans
    (congrArg (fun s : Set (PrimeSpectrum T.ring) => q ∈ s) he).symm.to_iff

end AlgebraicGeometry.Resolution.Blowups

namespace AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport.Construction

/-! Native closed-center support agrees with the displayed affine ideal at the chosen point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affine_center_le_prime_iff_global_support
    {X : Scheme.{0}} (I : X.IdealSheafData) (R : CommRingCat.{0}) (j : Spec R ⟶ X)
    (K : Ideal R) (hK : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K) (p : PrimeSpectrum R) :
    K ≤ p.asIdeal ↔ j p ∈ I.support := by
  have h := congrArg (fun L : (Spec R).IdealSheafData => (L.support : Set (Spec R))) hK
  rw [Scheme.IdealSheafData.support_comap, affineQuotientKernel_support] at h
  change p ∈ PrimeSpectrum.zeroLocus K ↔ p ∈ j ⁻¹' (I.support : Set X)
  exact (congrArg (fun S : Set (Spec R) => p ∈ S) h).symm.to_iff

end AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport.Construction

end

end OAI
