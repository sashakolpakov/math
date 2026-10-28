import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalLocalBasis
import OAI.AlgebraicGeometry.Resolution.Blowups.FreeConormalCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ExtendedQuotient

/-! # Affine Center Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineCenterBlowup.Construction

noncomputable section

/-! Any smooth closed center in a smooth Noetherian affine ambient scheme has a smooth actual blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem free_conormal_ideal_blowup_smooth
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.FormallySmooth k (R ⧸ I)]
    [Module.Free (R ⧸ I) I.Cotangent] :
    Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  classical
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  let : Algebra.Smooth k P.Ring := inferInstanceAs (Algebra.Smooth k R)
  let e := Blowups.Quotient.ConormalProjective.Construction.quotientExtensionCotangentEquiv (k := k) I
  let : Module.Free (R ⧸ I) P.Cotangent := Module.Free.of_equiv e.symm
  let : Module.Finite (R ⧸ I) I.Cotangent := Blowups.Quotient.ConormalProjective.Construction.smooth_quotient_conormal_finite I
  let : Module.Finite (R ⧸ I) P.Cotangent := Module.Finite.equiv e.symm
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) P.Cotangent
  let : Fintype ι := Fintype.ofFinite ι
  have hfg : P.ker.FG := by
    change (RingHom.ker (Ideal.Quotient.mk I)).FG
    rw [Ideal.mk_ker]
    exact Ideal.fg_of_isNoetherianRing I
  have h := FreeConormalCenterBlowup.Construction.free_conormal_center_blowup_smooth P (Module.Free.chooseBasis (R ⧸ I) P.Cotangent) hfg
  change Smooth (ReesGrading.Construction.affineBlowupToSpec (RingHom.ker (Ideal.Quotient.mk I)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R))) at h
  rwa [Ideal.mk_ker] at h

theorem smooth_affine_center_blowup_smooth
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)] :
    Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  classical
  apply Affine.BlowupSmoothOpenDescent.Construction.affineBlowup_smooth_of_pointed_open_bases k I
  intro p
  by_cases hIp : I ≤ p.asIdeal
  · obtain ⟨r, hr, hfree⟩ := ConormalLocalBasis.Construction.exists_smooth_center_conormal_free_neighborhood (k := k) I p.asIdeal hIp
    let S := Localization.Away r
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away r
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let : Algebra.Smooth k (S ⧸ I.map (algebraMap R S)) := ExtendedQuotient.Construction.smooth_extended_quotient I
    let : Module.Free (S ⧸ I.map (algebraMap R S)) (I.map (algebraMap R S)).Cotangent := hfree
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    obtain ⟨Q, hQ⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime r p hr
    exact ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization r, Q, hQ,
      free_conormal_ideal_blowup_smooth (I.map (algebraMap R S))⟩
  · obtain ⟨r, hrI, hrp⟩ := Set.not_subset.mp hIp
    let S := Localization.Away r
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away r
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    obtain ⟨Q, hQ⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime r p hrp
    refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization r, Q, hQ, ?_⟩
    have ht : I.map f.toRingHom = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I r hrI
    rw [ht]
    let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal S)) :=
      PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal S) ⟨1, trivial⟩ Ideal.span_singleton_one.symm isRegular_one
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k S))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap k S))).mpr
        (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineCenterBlowup.Construction
