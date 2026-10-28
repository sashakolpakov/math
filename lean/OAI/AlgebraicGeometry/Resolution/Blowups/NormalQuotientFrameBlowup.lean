import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseFiniteFrameCorrection
import OAI.AlgebraicGeometry.Resolution.Blowups.JacobianNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.QuotientPairBlowup

/-! # Normal Quotient Frame Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientFrameBlowup.Construction

noncomputable section

/-! Any finite coordinate center on a smooth normal quotient lifts to a smooth actual ambient blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem normal_quotient_frame_blowup_smooth
    {k R ι : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [Fintype ι] [DecidableEq ι]
    (z : R) (g : ι → R) (D : Derivation k R R) (hDz : D z = 1)
    (δ : ι → Derivation k (R ⧸ Ideal.span {z}) (R ⧸ Ideal.span {z}))
    (hδ : ∀ i j, δ i (Ideal.Quotient.mk (Ideal.span {z}) (g j)) = if i = j then 1 else 0) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (Ideal.span (Set.range g) ⊔ Ideal.span {z}) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  classical
  let q := Ideal.Quotient.mkₐ k (Ideal.span {z})
  have hqz : q z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)
  have hlift (i : ι) := Blowups.Smooth.ConormalDerivationLift.Construction.exists_quotient_derivation_lift_annihilating_normal k q
    Ideal.Quotient.mk_surjective (δ i) z hqz D hDz
  choose E hEz hE using hlift
  let a := (JacobianDerivationFrame.Construction.derivationJacobian E g).det
  have hqa : Ideal.Quotient.mk (Ideal.span {z}) a = 1 := by
    have hm : q.toRingHom.mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian E g) = 1 := by
      ext i j
      change q (E i (g j)) = (1 : Matrix ι ι (R ⧸ Ideal.span {z})) i j
      rw [hE, Matrix.one_apply]
      exact hδ i j
    change q.toRingHom (JacobianDerivationFrame.Construction.derivationJacobian E g).det = 1
    rw [RingHom.map_det, hm, Matrix.det_one]
  have hza : Ideal.span {z, a} = ⊤ := NormalQuotientDualPair.Construction.span_normal_pair_eq_top_of_quotient_one z a hqa
  let I := Ideal.span (Set.range g) ⊔ Ideal.span {z}
  apply Affine.BlowupSmoothOpenDescent.Construction.affineBlowup_smooth_of_pointed_open_bases k I
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
    let S := JacobianNeighborhood.Construction.derivationJacobianNeighborhood E g
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away a
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway a
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a p ha
    let g' : ι → S := fun i => f (g i)
    let E' := JacobianDerivationFrame.Construction.normalizedJacobianFrame (JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation E g) g'
    have hE'g : ∀ i j, E' i (g' j) = if i = j then 1 else 0 :=
      JacobianDerivationFrame.Construction.normalizedJacobianFrame_dual _ _ (JacobianNeighborhood.Construction.jacobianNeighborhood_jacobian_isUnit E g)
    have hE'z : ∀ i, E' i (f z) = 0 := by
      apply TransverseFiniteFrameCorrection.Construction.normalizedJacobianFrame_annihilates
      intro i
      change JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation E g i (algebraMap R S z) = 0
      rw [JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation_constants, hEz, map_zero]
    let D' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D
    have hD'z : D' (f z) = 1 := by
      change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D (algebraMap R S z) = 1
      rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hDz, map_one]
    obtain ⟨F, hFz, hFg⟩ := TransverseFiniteFrameCorrection.Construction.exists_normal_derivation_annihilating_frame D' E' g' (f z) hD'z hE'z hE'g
    have hs := DualFrameBlowupSmooth.Construction.dual_derivation_family_blowup_smooth (AdaptedEtaleFrame.Construction.transverseExtendedCoordinates g' (f z))
      (AdaptedEtaleFrame.Construction.transverseExtendedDerivations E' F (f z)) (AdaptedEtaleFrame.Construction.transverseExtendedDerivations_dual E' g' F (f z) hE'g hFz hFg)
    rw [TransverseFiniteFrameCorrection.Construction.transverseExtendedCoordinates_span] at hs
    refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization a, Q, hQ, ?_⟩
    change Smooth (ReesGrading.Construction.affineBlowupToSpec ((Ideal.span (Set.range g) ⊔ Ideal.span {z}).map f.toRingHom) ≫ _)
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, ← Set.range_comp]
    exact hs
  · let S := Localization.Away z
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away z
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime z p hz
    refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization z, Q, hQ, ?_⟩
    have hzI : z ∈ I := (show Ideal.span {z} ≤ I from le_sup_right) (Ideal.mem_span_singleton_self z)
    have ht : I.map f.toRingHom = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I z hzI
    rw [ht]
    let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal S)) :=
      PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal S) ⟨1, trivial⟩ Ideal.span_singleton_one.symm isRegular_one
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k S))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap k S))).mpr
        (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientFrameBlowup.Construction
