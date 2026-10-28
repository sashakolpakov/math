import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.QuotientPairBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenter

/-! # Center Blowup Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! The actual blowup of each finite-order surface coefficient center is smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem CenterBlowupSmooth.Construction.surface_lifted_curve_center_blowup_smooth
    (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R]
    (hd : ringKrullDim R ≤ 2) (I : Ideal R) (z : R) (D : Derivation k R R) (hDz : D z = 1)
    (hzI : z ∈ I) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k
      (I.map (Ideal.Quotient.mk (Ideal.span {z}))) = ⊤) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  classical
  apply Affine.BlowupSmoothOpenDescent.Construction.affineBlowup_smooth_of_pointed_open_bases k I
  intro p
  by_cases hIp : I ≤ p.asIdeal
  · obtain ⟨S, akS, f, hf, hs, Q, hQ, g, D', E', hgen, hDz', hDg', hEz', hEg'⟩ :=
      CenterPointedFrame.Construction.surface_center_pointed_dual_pair_neighborhood k hd I z D hDz hzI hI p hIp
    let : Algebra k S := akS
    let : Algebra.Smooth k S := hs
    refine ⟨S, akS, f, hf, Q, hQ, ?_⟩
    rw [hgen]
    exact DualPairBlowupSmooth.Construction.dual_pair_blowup_smooth (f z) g D' E' hDz' hDg' hEz' hEg'
  · obtain ⟨a, haI, hap⟩ := Set.not_subset.mp hIp
    let S := Localization.Away a
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away a
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    obtain ⟨Q, hQ⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime a p hap
    refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization a, Q, hQ, ?_⟩
    have htop : I.map f.toRingHom = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I a haI
    rw [htop]
    let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal S)) :=
      PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal S) ⟨1, trivial⟩ Ideal.span_singleton_one.symm isRegular_one
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k S))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap k S))).mpr
        (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance

theorem TangentCenterChoice.Construction.SurfaceTangentCenterChoice.blowup_smooth
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R]
    {J : Ideal R} {n ℓ : ℕ} (C : TangentCenterChoice.Construction.SurfaceTangentCenterChoice k R J n ℓ)
    (hd : ringKrullDim R ≤ 2) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec C.center ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  cases C with
  | terminal _ =>
      change Smooth (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal R) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))
      let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal R)) :=
        PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal R) ⟨1, trivial⟩ Ideal.span_singleton_one.symm isRegular_one
      let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
        (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap k R))).mpr
          (RingHom.smooth_algebraMap.mpr inferInstance)
      infer_instance
  | normal z D hD _ hb =>
      apply CenterBlowupSmooth.Construction.surface_lifted_curve_center_blowup_smooth k hd _ z D hD
      · exact Coefficient.TangentNaturality.Construction.coefficientTangentCenter_normal_mem k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
      · change Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k
          ((Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ).map
            (Ideal.Quotient.mk (Ideal.span {z}))) = ⊤
        rw [Coefficient.TangentNaturality.Construction.coefficientTangentCenter_quotient, Curve.IntrinsicStep.Construction.first_iteratedRelativeDifferentialIdeal]
        exact hb

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
