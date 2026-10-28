import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDualPair
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupSmoothOpenDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientCenter

/-! # Quotient Pair Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.QuotientPairBlowup.Construction

noncomputable section

/-! An ambient normal and a smooth quotient coordinate give a smooth actual two-equation blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem normal_quotient_coordinate_blowup_smooth
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (z g : R) (D : Derivation k R R) (hDz : D z = 1)
    (δ : Derivation k (R ⧸ Ideal.span {z}) (R ⧸ Ideal.span {z}))
    (hδ : δ (Ideal.Quotient.mk (Ideal.span {z}) g) = 1) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (Ideal.span {z, g}) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let q := Ideal.Quotient.mkₐ k (Ideal.span {z})
  have hqz : q z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)
  obtain ⟨E, hEz, hE⟩ := ConormalDerivationLift.Construction.exists_quotient_derivation_lift_annihilating_normal k q
    Ideal.Quotient.mk_surjective δ z hqz D hDz
  let a := E g
  have hqa : Ideal.Quotient.mk (Ideal.span {z}) a = 1 := (hE g).trans hδ
  have hza : Ideal.span {z, a} = ⊤ := NormalQuotientDualPair.Construction.span_normal_pair_eq_top_of_quotient_one z a hqa
  apply Affine.BlowupSmoothOpenDescent.Construction.affineBlowup_smooth_of_pointed_open_bases k (Ideal.span {z, g})
  intro p
  by_cases hz : z ∈ p.asIdeal
  · have ha : a ∉ p.asIdeal := by
      intro ha
      have hle : Ideal.span {z, a} ≤ p.asIdeal := Ideal.span_le.mpr (by
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact hz
        · exact Set.mem_singleton_iff.mp hx ▸ ha)
      rw [hza] at hle
      exact p.isPrime.ne_top (top_le_iff.mp hle)
    let S := Localization.Away a
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away a
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway a
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a p ha
    let D' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D
    let E' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E
    have hD'z : D' (f z) = 1 := by
      change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D (algebraMap R S z) = 1
      rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hDz, map_one]
    have hE'z : E' (f z) = 0 := by
      change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E (algebraMap R S z) = 0
      rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hEz, map_zero]
    have hE'g : IsUnit (E' (f g)) := by
      change IsUnit (Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E (algebraMap R S g))
      rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
      exact IsLocalization.Away.algebraMap_isUnit a
    obtain ⟨D'', E'', hDz', hDg', hEz', hEg'⟩ := NormalQuotientDualPair.Construction.exists_dual_pair_of_transverse_unit
      (f z) (f g) D' E' hD'z hE'z hE'g
    refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization a, Q, hQ, ?_⟩
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    exact DualPairBlowupSmooth.Construction.dual_pair_blowup_smooth (f z) (f g) D'' E'' hDz' hDg' hEz' hEg'
  · let S := Localization.Away z
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away z
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime z p hz
    refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization z, Q, hQ, ?_⟩
    have htop : (Ideal.span {z, g}).map f.toRingHom = ⊤ :=
      IdempotentQuotientCenter.Construction.center_map_away_member_eq_top (Ideal.span {z, g}) z (Ideal.subset_span (by simp))
    rw [htop]
    let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal S)) :=
      PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal S) ⟨1, trivial⟩ Ideal.span_singleton_one.symm isRegular_one
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k S))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap k S))).mpr
        (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.QuotientPairBlowup.Construction
