import OAI.AlgebraicGeometry.Resolution.Blowups.ConormalBasisDerivations
import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientFrameBlowup

/-! # Free Conormal Center Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FreeConormalCenterBlowup.Construction

noncomputable section

/-! A finite conormal basis supplies actual open coordinate frames and a smooth entire blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem free_conormal_center_blowup_smooth
    {k Q ι : Type u} [CommRing k] [CommRing Q] [Algebra k Q]
    (P : Algebra.Extension.{u} k Q) [Algebra.Smooth k P.Ring] [Algebra.FormallySmooth k Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι Q P.Cotangent) (hfg : P.ker.FG) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec P.ker ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.Ring))) := by
  classical
  obtain ⟨g, E, hgen, hE⟩ := ConormalBasisDerivations.Construction.exists_conormal_basis_generators_and_derivations P b
  let v : ι → P.Ring := fun i => (g i).val
  let G := Ideal.span (Set.range v)
  have hGI : G ≤ P.ker := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (g i).property)
  obtain ⟨r, hr, hlocal⟩ := ConormalBasisDerivations.Construction.exists_center_generator_principal_neighborhood P.ker G hfg hGI hgen.le
  let a := (JacobianDerivationFrame.Construction.derivationJacobian E v).det
  have hqa : algebraMap P.Ring Q a = 1 := by
    have hm : (algebraMap P.Ring Q).mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian E v) = 1 := by
      ext i j
      change algebraMap P.Ring Q (E i (g j).val) = (1 : Matrix ι ι Q) i j
      rw [hE, Matrix.one_apply]
    change algebraMap P.Ring Q (JacobianDerivationFrame.Construction.derivationJacobian E v).det = 1
    rw [RingHom.map_det, hm, Matrix.det_one]
  have haI : a - 1 ∈ P.ker := RingHom.mem_ker.mpr (by rw [map_sub, hqa, map_one, sub_self])
  apply Affine.BlowupSmoothOpenDescent.Construction.affineBlowup_smooth_of_pointed_open_bases k P.ker
  intro p
  by_cases hIp : P.ker ≤ p.asIdeal
  · have hrp : r ∉ p.asIdeal := ConormalBasisDerivations.Construction.generator_neighborhood_avoids_center_prime P.ker p.asIdeal hIp r hr
    have hap : a ∉ p.asIdeal := ConormalBasisDerivations.Construction.generator_neighborhood_avoids_center_prime P.ker p.asIdeal hIp a haI
    let A := Localization.Away r
    let : Algebra.Smooth P.Ring A := Algebra.Smooth.of_isLocalization_Away r
    let : Algebra.Smooth k A := Algebra.Smooth.comp k P.Ring A
    let : Algebra.Etale P.Ring A := Algebra.Etale.of_isLocalizationAway r
    let fA : P.Ring →ₐ[k] A := IsScalarTower.toAlgHom k P.Ring A
    obtain ⟨pA, hpA⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime r p hrp
    let EA : ι → Derivation k A A := fun i => Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) (E i)
    let vA : ι → A := fun i => fA (v i)
    have hdet : (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det = fA a := by
      have hm : JacobianDerivationFrame.Construction.derivationJacobian EA vA = fA.toRingHom.mapMatrix (JacobianDerivationFrame.Construction.derivationJacobian E v) := by
        ext i j
        exact Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (E i) (v j)
      rw [hm, ← RingHom.map_det]
      rfl
    have hdetp : (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det ∉ pA.asIdeal := by
      rw [hdet]
      have he : pA.asIdeal.comap fA.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
      change a ∉ pA.asIdeal.comap fA.toRingHom
      rwa [he]
    let S := JacobianNeighborhood.Construction.derivationJacobianNeighborhood EA vA
    let : Algebra.Smooth A S := Algebra.Smooth.of_isLocalization_Away (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det
    let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
    let fS : A →ₐ[k] S := IsScalarTower.toAlgHom k A S
    let f : P.Ring →ₐ[k] S := fS.comp fA
    obtain ⟨Q', hQ'⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det pA hdetp
    let w : ι → S := fun i => algebraMap A S (vA i)
    let F := JacobianDerivationFrame.Construction.normalizedJacobianFrame (JacobianNeighborhood.Construction.jacobianNeighborhoodDerivation EA vA) w
    have hF : ∀ i j, F i (w j) = if i = j then 1 else 0 :=
      JacobianDerivationFrame.Construction.normalizedJacobianFrame_dual _ _ (JacobianNeighborhood.Construction.jacobianNeighborhood_jacobian_isUnit EA vA)
    refine ⟨.of S, inferInstance, f, ?_, Q', ?_, ?_⟩
    · let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P.Ring A))) :=
        IsOpenImmersion.of_isLocalization r
      let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
        IsOpenImmersion.of_isLocalization (JacobianDerivationFrame.Construction.derivationJacobian EA vA).det
      change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap P.Ring A) ≫
        CommRingCat.ofHom (algebraMap A S)))
      rw [Spec.map_comp]
      infer_instance
    · apply PrimeSpectrum.ext
      change (Q'.asIdeal.comap (algebraMap A S)).comap (algebraMap P.Ring A) = p.asIdeal
      have hQI : Q'.asIdeal.comap (algebraMap A S) = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hQ'
      rw [hQI]
      exact congrArg PrimeSpectrum.asIdeal hpA
    · have hi : P.ker.map f.toRingHom = Ideal.span (Set.range w) := by
        change P.ker.map ((algebraMap A S).comp (algebraMap P.Ring A)) = _
        rw [← Ideal.map_map, hlocal, Ideal.map_map]
        dsimp only [G]
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      rw [hi]
      exact DualFrameBlowupSmooth.Construction.dual_derivation_family_blowup_smooth w F hF
  · obtain ⟨s, hsI, hsp⟩ := Set.not_subset.mp hIp
    let S := Localization.Away s
    let : Algebra.Smooth P.Ring S := Algebra.Smooth.of_isLocalization_Away s
    let : Algebra.Smooth k S := Algebra.Smooth.comp k P.Ring S
    let f : P.Ring →ₐ[k] S := IsScalarTower.toAlgHom k P.Ring S
    obtain ⟨Q', hQ'⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime s p hsp
    refine ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization s, Q', hQ', ?_⟩
    have ht : P.ker.map f.toRingHom = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top P.ker s hsI
    rw [ht]
    let : IsIso (ReesGrading.Construction.affineBlowupToSpec (⊤ : Ideal S)) :=
      PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal S) ⟨1, trivial⟩ Ideal.span_singleton_one.symm isRegular_one
    let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k S))) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap k S))).mpr
        (RingHom.smooth_algebraMap.mpr inferInstance)
    infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FreeConormalCenterBlowup.Construction
