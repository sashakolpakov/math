import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterReplacementFrame

/-! # Center Normal Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterNormalFrame.Construction

noncomputable section

/-! Actual local frames of arbitrary smooth centers can retain a prescribed smooth normal equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_center_pointed_open_frame_retaining_normal
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (z : R) (hzI : z ∈ I) (E : Derivation k R R) (hEz : E z = 1)
    (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
        (v : Option ι → S) (D : Option ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        v none = f z ∧ I.map f.toRingHom = Ideal.span (Set.range v) := by
  classical
  obtain ⟨A, hAk, hAs, g, hgOpen, pA, hpA, ι, hι, hdec, v, D, hD, hI⟩ :=
    CenterPointedFrame.Construction.smooth_center_pointed_open_frame (k := k) I p hIp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) := hgOpen
  have hg : g.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom g.toRingHom)).mp inferInstance
  let : Algebra R A := g.toRingHom.toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  let : Algebra.Etale R A := RingHom.etale_algebraMap.mp hg
  let EA : Derivation k A A := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E
  have hEA : EA (g z) = 1 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E (algebraMap R A z) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hEz, map_one]
  have hvp (i : ι) : v i ∈ pA.asIdeal := by
    have hi : I.map g.toRingHom ≤ pA.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      have he : pA.asIdeal.comap g.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
      rwa [he]
    apply hi
    rw [hI]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hzv : g z ∈ Ideal.span (Set.range v) := hI ▸ Ideal.mem_map_of_mem g.toRingHom hzI
  obtain ⟨c, i, hc, hci, hDi⟩ := Boundary.CenterPivot.Construction.exists_boundary_center_pivot v D hD (g z) hzv EA pA.asIdeal hvp
    (by rw [hEA]; exact pA.isPrime.one_notMem)
  let r : A := c i * D i (g z)
  have hr : r ∉ pA.asIdeal := pA.asIdeal.primeCompl.mul_mem hci hDi
  let S := Localization.Away r
  let : Algebra.Etale A S := Algebra.Etale.of_isLocalizationAway r
  let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
  let a : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let f : R →ₐ[k] S := a.comp g
  let vS : ι → S := fun j => a (v j)
  let DS : ι → Derivation k S S := fun j => Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (D j)
  have hDS : ∀ j l, DS j (vS l) = if j = l then 1 else 0 := by
    intro j l
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (D j) (algebraMap A S (v l)) = _
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD]
    split_ifs <;> simp
  have hu : IsUnit (a (c i) * a (D i (g z))) := by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit r
  have hdu : IsUnit (DS i (f z)) := by
    change IsUnit (Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (D i) (algebraMap A S (g z)))
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
    exact isUnit_of_mul_isUnit_right hu
  obtain ⟨F, hF⟩ := Boundary.CenterReplacementFrame.Construction.exists_centerReplacement_dual_frame vS DS hDS i (f z) hdu
  have hcoeff : (∑ j, a (c j) * vS j) = f z := by
    simpa only [map_sum, map_mul, vS, f, AlgHom.comp_apply] using congrArg a hc
  have hspan := CenterGeneratorReplacement.Construction.centerReplacementFamily_span vS (fun j => a (c j)) i (f z) hcoeff
    (isUnit_of_mul_isUnit_left hu)
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r pA hr
  refine ⟨.of S, inferInstance, inferInstance, f,
    ?_,
    q, ?_, {j : ι // i ≠ j}, inferInstance, inferInstance,
    CenterGeneratorReplacement.Construction.centerReplacementFamily vS i (f z), F, hF, rfl, ?_⟩
  · let : IsOpenImmersion (Spec.map (CommRingCat.ofHom a.toRingHom)) :=
        IsOpenImmersion.of_isLocalization r
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom a.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change (q.asIdeal.comap a.toRingHom).comap g.toRingHom = p.asIdeal
    have he : q.asIdeal.comap a.toRingHom = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [he]
    exact congrArg PrimeSpectrum.asIdeal hpA
  · rw [hspan]
    change I.map (a.toRingHom.comp g.toRingHom) = _
    rw [← Ideal.map_map, hI, Ideal.map_span, ← Set.range_comp]
    rfl

theorem smooth_center_pointed_frame_retaining_normal
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (z : R) (hzI : z ∈ I) (E : Derivation k R R) (hEz : E z = 1)
    (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), f.toRingHom.Etale ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
        (v : Option ι → S) (D : Option ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        v none = f z ∧ I.map f.toRingHom = Ideal.span (Set.range v) := by
  obtain ⟨S, hSk, hSs, f, hf, rest⟩ := smooth_center_pointed_open_frame_retaining_normal (k := k) I z hzI E hEz p hIp
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  exact ⟨S, hSk, hSs, f,
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance,
    rest⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterNormalFrame.Construction
