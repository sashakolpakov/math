import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterIncidence

/-! # Prime Center Boundary Incidence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An integral affine center determines its containing boundary labels independently of the pointed chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem PrimeCenterBoundaryIncidence.Construction.flat_prime_ideal_mem_iff {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (I : Ideal R) [I.IsPrime]
    (hproper : I.map φ ≠ ⊤) (x : R) : φ x ∈ I.map φ ↔ x ∈ I := by
  constructor
  · intro hx
    by_contra hxi
    let : Algebra R S := φ.toAlgebra
    let : Module.Flat R S := hφ
    have hr : IsRegular (Ideal.Quotient.mk I x) :=
      IsRegular.of_ne_zero (fun h => hxi (Ideal.Quotient.eq_zero_iff_mem.mp h))
    have hs := FlatQuotientRegularity.Construction.flat_extended_quotient_regular (S := S) I x hr
    have hz : Ideal.Quotient.mk (I.map φ) (φ x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hone : Ideal.Quotient.mk (I.map φ) (1 : S) = 0 := by
      change (1 : S ⧸ I.map φ) = 0
      apply hs.left
      change Ideal.Quotient.mk (I.map φ) (φ x) * 1 = Ideal.Quotient.mk (I.map φ) (φ x) * 0
      rw [hz, zero_mul, zero_mul]
    exact hproper ((Ideal.eq_top_iff_one _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hone))
  · exact Ideal.mem_map_of_mem φ

theorem MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.divided_iff_mem_prime_center
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    (I : Ideal R) [I.IsPrime] {ι : Type v} {w : ι → R} {F : Finset ι} {p : PrimeSpectrum R}
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p) (hp : I ≤ p.asIdeal) (j : ι) :
    j ∈ F ↔ w j ∈ I := by
  have hle : I.map C.chart.map.toRingHom ≤ C.chart.point.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    have he := congrArg PrimeSpectrum.asIdeal C.chart.point_over
    change C.chart.point.asIdeal.comap C.chart.map.toRingHom = p.asIdeal at he
    rw [he]
    exact hp
  have hproper : I.map C.chart.map.toRingHom ≠ ⊤ := by
    intro h
    exact C.chart.point.isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  have hf : Flat (Spec.map (CommRingCat.ofHom C.chart.map.toRingHom)) := inferInstance
  exact (C.divided_iff_mem I hp j).trans (PrimeCenterBoundaryIncidence.Construction.flat_prime_ideal_mem_iff C.chart.map.toRingHom
    ((HasRingHomProperty.Spec_iff (P := @Flat)).mp hf) I hproper (w j))

theorem PrimeCenterBoundaryIncidence.Construction.prime_center_boundary_incidence_independent
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    (I : Ideal R) [I.IsPrime] {ι : Type v} {w : ι → R} {F G : Finset ι}
    {p q : PrimeSpectrum R} (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p)
    (D : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w G q)
    (hp : I ≤ p.asIdeal) (hq : I ≤ q.asIdeal) : F = G := by
  ext j
  exact (C.divided_iff_mem_prime_center I hp j).trans (D.divided_iff_mem_prime_center I hq j).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
