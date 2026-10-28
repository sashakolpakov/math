import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.RegularHypersurfaceNormal
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterNormalFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.FramedHypersurfaceTransformSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentBlowupCharts

/-! # Hypersurface Transform Neighborhoods -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.HypersurfaceTransformNeighborhoods.Construction

noncomputable section

/-! Actual pointed open generating charts make the transform of a smooth regular hypersurface smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem unit_center_controlled_quotient_smooth
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (I J : Ideal R) (hI : I = ⊤) [Algebra.Smooth k (R ⧸ J)] (b : ℕ) (a : I) :
    Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a ⧸ ControlledTransform.Construction.blowupControlledTransform I J b a) := by
  subst I
  have ht : IsIdempotentElem (⊤ : Ideal R) := by simp [IsIdempotentElem]
  rw [IdempotentBlowupCharts.Construction.idempotent_blowup_controlledTransform ⊤ J ht a b]
  let : Algebra R (Blowup.Charts.Construction.blowupChart ⊤ a) := (Blowup.Charts.Construction.blowupChartConstants ⊤ a).toAlgebra
  let : SMul R (Blowup.Charts.Construction.blowupChart ⊤ a) := (Blowup.Charts.Construction.blowupChartConstants ⊤ a).toAlgebra.toSMul
  let : IsScalarTower k R (Blowup.Charts.Construction.blowupChart ⊤ a) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := R) (A := Blowup.Charts.Construction.blowupChart ⊤ a) (fun _ => rfl)
  let : Algebra.Etale R (Blowup.Charts.Construction.blowupChart ⊤ a) :=
    RingHom.etale_algebraMap.mp (IdempotentBlowupCharts.Construction.idempotent_blowupChartConstants_etale ⊤ ht a)
  exact TransformedCoordinateHypersurface.Construction.smooth_etale_extended_quotient J

theorem smooth_hypersurface_transform_pointed_generators
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (z : R) (hz : IsRegular z) [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    (hzI : z ∈ I) (p : PrimeSpectrum R) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (κ : Type u) (g : κ → I.map f.toRingHom),
        Ideal.span (Set.range (fun a => (g a).val)) = I.map f.toRingHom ∧
        ∀ a, Algebra.Smooth k (Blowup.Charts.Construction.blowupChart (I.map f.toRingHom) (g a) ⧸
          ControlledTransform.Construction.blowupControlledTransform (I.map f.toRingHom) ((Ideal.span {z}).map f.toRingHom) 1 (g a)) := by
  classical
  by_cases hIp : I ≤ p.asIdeal
  · obtain ⟨A, aA, hsA, φ, hopen, pA, hpA, E, hE⟩ :=
      RegularHypersurfaceNormal.Construction.smooth_regular_hypersurface_pointed_open_normal (k := k) z hz p (hIp hzI)
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hopen
    have hφ : φ.toRingHom.Etale :=
      (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom φ.toRingHom)).mp inferInstance
    let : Algebra R A := φ.toRingHom.toAlgebra
    let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    let : Algebra.Etale R A := RingHom.etale_algebraMap.mp hφ
    let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
    let : Algebra.Smooth k (A ⧸ I.map φ.toRingHom) := TransformedCoordinateHypersurface.Construction.smooth_etale_extended_quotient I
    have hIA : I.map φ.toRingHom ≤ pA.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      have he : pA.asIdeal.comap φ.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
      rwa [he]
    obtain ⟨S, aS, hsS, ψ, hopenS, q, hq, ι, hι, hdec, w, D, hD, hw, hgen⟩ :=
      CenterNormalFrame.Construction.smooth_center_pointed_open_frame_retaining_normal (k := k) (I.map φ.toRingHom) (φ z)
        (Ideal.mem_map_of_mem _ hzI) E hE pA hIA
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := hopenS
    let f := ψ.comp φ
    have hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
      change IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom ψ.toRingHom))
      rw [Spec.map_comp]
      infer_instance
    have hI : I.map f.toRingHom = Ideal.span (Set.range w) := by
      change I.map (ψ.toRingHom.comp φ.toRingHom) = _
      rw [← Ideal.map_map]
      exact hgen
    let g : Option ι → I.map f.toRingHom := fun a => ⟨w a, hI.symm ▸ Ideal.subset_span ⟨a, rfl⟩⟩
    have hg : Ideal.span (Set.range (fun a => (g a).val)) = I.map f.toRingHom := hI.symm
    have hnormal : (Ideal.span {z}).map f.toRingHom = Ideal.span {(g none).val} := by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {f z} = Ideal.span {w none}
      rw [hw]
      rfl
    refine ⟨S, aS, hsS, f, hf, q, ?_, Option ι, g, hg, ?_⟩
    · apply PrimeSpectrum.ext
      change (q.asIdeal.comap ψ.toRingHom).comap φ.toRingHom = p.asIdeal
      have he : q.asIdeal.comap ψ.toRingHom = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hq
      rw [he]
      exact congrArg PrimeSpectrum.asIdeal hpA
    · intro a
      rw [hnormal]
      exact FramedHypersurfaceTransformSmooth.Construction.framed_coordinate_controlled_quotient_smooth (I.map f.toRingHom) g D hD hg a none
  · obtain ⟨r, hrI, hrp⟩ := Set.not_subset.mp hIp
    let S := Localization.Away r
    let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway r
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    have hI : I.map f.toRingHom = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I r hrI
    let : Algebra.Smooth k (S ⧸ (Ideal.span {z}).map f.toRingHom) := TransformedCoordinateHypersurface.Construction.smooth_etale_extended_quotient (Ideal.span {z})
    obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r p hrp
    refine ⟨.of S, inferInstance, inferInstance, f, IsOpenImmersion.of_isLocalization r,
      q, hq, I.map f.toRingHom, id, ?_, ?_⟩
    · change Ideal.span (Set.range (Subtype.val : I.map f.toRingHom → S)) = _
      rw [Subtype.range_val, Ideal.span_eq]
    · intro a
      exact unit_center_controlled_quotient_smooth (I.map f.toRingHom) ((Ideal.span {z}).map f.toRingHom) hI 1 a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.HypersurfaceTransformNeighborhoods.Construction
