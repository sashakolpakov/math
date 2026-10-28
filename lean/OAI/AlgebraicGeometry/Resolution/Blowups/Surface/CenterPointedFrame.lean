import OAI.AlgebraicGeometry.Resolution.Blowups.DualPairQuotientDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.GeneralIdempotentQuotientCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDualPair
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Center Pointed Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.CenterPointedFrame.Construction

noncomputable section

/-! Actual open two-equation frames for lifted smooth curve centers on a smooth surface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R]

theorem surface_center_pointed_dual_pair_neighborhood
    (hd : ringKrullDim R ≤ 2) (I : Ideal R) (z : R) (D : Derivation k R R) (hDz : D z = 1)
    (hzI : z ∈ I) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k
      (I.map (Ideal.Quotient.mk (Ideal.span {z}))) = ⊤)
    (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (f : R →ₐ[k] S),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧ Algebra.Smooth k S ∧
      ∃ Q : PrimeSpectrum S, PrimeSpectrum.comap f.toRingHom Q = p ∧
      ∃ (g : S) (D' E' : Derivation k S S),
        I.map f.toRingHom = Ideal.span {f z, g} ∧
        D' (f z) = 1 ∧ D' g = 0 ∧ E' (f z) = 0 ∧ E' g = 1 := by
  let q := Ideal.Quotient.mkₐ k (Ideal.span {z})
  have hzp : Ideal.span {z} ≤ p.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr (hIp hzI)
  let pbar : Ideal (R ⧸ Ideal.span {z}) := p.asIdeal.map q.toRingHom
  let : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hzp
  have hpbar : pbar.comap q.toRingHom = p.asIdeal := by
    change (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {z}))).comap
      (Ideal.Quotient.mk (Ideal.span {z})) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hzp]
  obtain ⟨δ, gbar, hgbar⟩ := Curve.CenterPointedFrame.Construction.exists_derivative_outside_center_prime k (I.map q.toRingHom)
    pbar (Ideal.map_mono hIp) hI
  obtain ⟨g, hgI, hqg⟩ := (Ideal.mem_map_iff_of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).mp gbar.property
  change q g = gbar.val at hqg
  have hqz : q z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)
  obtain ⟨E, hEz, hE⟩ := Blowups.Smooth.ConormalDerivationLift.Construction.exists_quotient_derivation_lift_annihilating_normal k q
    Ideal.Quotient.mk_surjective δ z hqz D hDz
  let a := E g
  have ha : a ∉ p.asIdeal := by
    intro ha
    have hqa : q a ∈ pbar := by
      change a ∈ pbar.comap q.toRingHom
      rwa [hpbar]
    rw [hE g, hqg] at hqa
    exact hgbar hqa
  let A := Localization.Away a
  let : Algebra.Smooth R A := Algebra.Smooth.of_isLocalization_Away a
  let : Algebra.Smooth k A := Algebra.Smooth.comp k R A
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway a
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let fA : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  obtain ⟨pA, hpA⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a p ha
  have hpAI : pA.asIdeal.comap fA.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
  let DA := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) D
  let EA := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E
  have hDA : DA (fA z) = 1 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) D (algebraMap R A z) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hDz, map_one]
  have hEA : EA (fA z) = 0 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E (algebraMap R A z) = 0
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hEz, map_zero]
  have hEAg : IsUnit (EA (fA g)) := by
    change IsUnit (Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) E (algebraMap R A g))
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
    exact IsLocalization.Away.algebraMap_isUnit a
  obtain ⟨D0, E0, hD0z, hD0g, hE0z, hE0g⟩ := NormalQuotientDualPair.Construction.exists_dual_pair_of_transverse_unit
    (fA z) (fA g) DA EA hDA hEA hEAg
  let K : Ideal A := Ideal.span {fA z, fA g}
  have hKI : K ≤ I.map fA.toRingHom := Ideal.span_le.mpr (by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Ideal.mem_map_of_mem _ hzI
    · exact Set.mem_singleton_iff.mp hx ▸ Ideal.mem_map_of_mem _ hgI)
  let : Algebra.Smooth k (A ⧸ K) := DualPairQuotientDimension.Construction.transverse_pair_quotient_smooth
    (fA z) (fA g) D0 E0 hD0z hE0z hE0g
  let : IsReduced (A ⧸ K) := Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k
  have hdA : ringKrullDim A ≤ 2 := (HypersurfaceDimension.Construction.localization_ringKrullDim_le (B := A) (Submonoid.powers a)).trans hd
  have hdK : ringKrullDim (A ⧸ K) ≤ 0 :=
    DualPairQuotientDimension.Construction.transverse_pair_quotient_dimension (fA z) (fA g) D0 E0 hD0z hE0z hE0g 0 hdA
  obtain ⟨r, hr, hgen, hrel⟩ := GeneralIdempotentQuotientCenter.Construction.zero_dimensional_quotient_center_generators K hdK
    (I.map fA.toRingHom) hKI
  have hrp : r ∈ pA.asIdeal := (Ideal.map_le_iff_le_comap.mpr (hpAI.symm ▸ hIp)) hr
  have hcomp : 1 - r ∉ pA.asIdeal := by
    intro h
    have hone := pA.asIdeal.add_mem h hrp
    rw [sub_add_cancel] at hone
    exact pA.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  let S := Localization.Away (1 - r)
  let : Algebra.Smooth A S := Algebra.Smooth.of_isLocalization_Away (1 - r)
  let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
  let : Algebra.Etale A S := Algebra.Etale.of_isLocalizationAway (1 - r)
  let fS : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
  let f : R →ₐ[k] S := fS.comp fA
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime (1 - r) pA hcomp
  let D' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D0
  let E' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E0
  refine ⟨.of S, inferInstance, f, ?_, inferInstance, Q, ?_, f g, D', E', ?_, ?_, ?_, ?_, ?_⟩
  · let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      IsOpenImmersion.of_isLocalization a
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
      IsOpenImmersion.of_isLocalization (1 - r)
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom (algebraMap A S)))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change (Q.asIdeal.comap (algebraMap A S)).comap (algebraMap R A) = p.asIdeal
    have hQI : Q.asIdeal.comap (algebraMap A S) = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hQ
    rw [hQI]
    exact hpAI
  · change I.map ((algebraMap A S).comp fA.toRingHom) = _
    rw [← Ideal.map_map, GeneralIdempotentQuotientCenter.Construction.idempotent_general_quotient_center_map_complement _ K r hgen hrel]
    dsimp only [K]
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rfl
  · change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D0 (algebraMap A S (fA z)) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD0z, map_one]
  · change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D0 (algebraMap A S (fA g)) = 0
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD0g, map_zero]
  · change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E0 (algebraMap A S (fA z)) = 0
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hE0z, map_zero]
  · change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E0 (algebraMap A S (fA g)) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hE0g, map_one]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.CenterPointedFrame.Construction
