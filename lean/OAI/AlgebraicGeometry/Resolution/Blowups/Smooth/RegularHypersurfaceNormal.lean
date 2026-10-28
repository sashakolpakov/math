import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.ChartFlatBaseChange

/-! # Regular Hypersurface Normal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.RegularHypersurfaceNormal.Construction

noncomputable section

/-! A regular smooth hypersurface has an actual pointed étale neighborhood with a normalized normal derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_regular_hypersurface_pointed_open_normal
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (z : R) (hz : IsRegular z)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] (p : PrimeSpectrum R) (hzp : z ∈ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ D : Derivation k S S, D (f z) = 1 := by
  classical
  let I := Ideal.span {z}
  have hIp : I ≤ p.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hzp
  obtain ⟨A, hAk, hAs, g, hgOpen, pA, hpA, ι, hι, hdec, v, D, hD, hI⟩ :=
    CenterPointedFrame.Construction.smooth_center_pointed_open_frame (k := k) I p hIp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := hgOpen
  have hg : g.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom g.toRingHom)).mp inferInstance
  let : Algebra R A := g.toRingHom.toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  let : Algebra.Etale R A := RingHom.etale_algebraMap.mp hg
  have hreg : IsRegular (g z) := ChartFlatBaseChange.Construction.flat_algebraMap_regular z hz
  have hzA : g z ∈ pA.asIdeal := by
    have he : pA.asIdeal.comap g.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
    change z ∈ pA.asIdeal.comap g.toRingHom
    rwa [he]
  have hspan : Ideal.span (Set.range v) = Ideal.span {g z} := by
    rw [← hI]
    change (Ideal.span {z}).map g.toRingHom = _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hnonempty : Nonempty ι := by
    by_contra hn
    have hempty : Set.range v = ∅ := Set.range_eq_empty_iff.mpr (not_nonempty_iff.mp hn)
    have hz0 : g z = 0 := by
      have hm := Ideal.mem_span_singleton_self (g z)
      rw [← hspan, hempty, Ideal.span_empty] at hm
      exact hm
    have hone : (1 : A) = 0 := hreg.left (by rw [hz0]; simp)
    apply pA.isPrime.one_notMem
    rw [hone]
    exact pA.asIdeal.zero_mem
  let i : ι := Classical.choice hnonempty
  have hv : v i ∈ Ideal.span {g z} := hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hv
  have hdiff : D i (g z) ∉ pA.asIdeal := by
    intro hd
    have hder := congrArg (D i) ha
    rw [Derivation.leibniz, hD, ite_eq_left rfl] at hder
    have hm : g z * D i a + a * D i (g z) ∈ pA.asIdeal :=
      pA.asIdeal.add_mem (pA.asIdeal.mul_mem_right _ hzA) (pA.asIdeal.mul_mem_left _ hd)
    exact pA.isPrime.one_notMem (hder ▸ hm)
  let r := D i (g z)
  let S := Localization.Away r
  let : Algebra.Etale A S := Algebra.Etale.of_isLocalizationAway r
  let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
  let α : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let f := α.comp g
  let E := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (D i)
  have hunit : IsUnit (E (f z)) := by
    change IsUnit (Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (D i) (algebraMap A S (g z)))
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
    exact IsLocalization.Away.algebraMap_isUnit r
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r pA hdiff
  refine ⟨.of S, inferInstance, inferInstance, f,
    ?_, q, ?_,
    (u⁻¹ : Sˣ) • E, ?_⟩
  · let : IsOpenImmersion (Spec.map (CommRingCat.ofHom α.toRingHom)) :=
        IsOpenImmersion.of_isLocalization r
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom α.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change (q.asIdeal.comap α.toRingHom).comap g.toRingHom = p.asIdeal
    have he : q.asIdeal.comap α.toRingHom = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [he]
    exact congrArg PrimeSpectrum.asIdeal hpA
  · change (↑u⁻¹ : S) * E (f z) = 1
    rw [← hu]
    exact Units.inv_mul u

theorem smooth_regular_hypersurface_pointed_normal
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (z : R) (hz : IsRegular z)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] (p : PrimeSpectrum R) (hzp : z ∈ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), f.toRingHom.Etale ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ D : Derivation k S S, D (f z) = 1 := by
  obtain ⟨S, hSk, hSs, f, hf, rest⟩ := smooth_regular_hypersurface_pointed_open_normal (k := k) z hz p hzp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  exact ⟨S, hSk, hSs, f,
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance,
    rest⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.RegularHypersurfaceNormal.Construction
