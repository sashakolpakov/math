import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorSequenceTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComaximalFactor
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComponentBoundaryAtlas

/-! # Center Factor Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CenterFactorSequence.Construction

noncomputable section

/-! A finite disjoint factorization of a smooth center replaces its blowup by actual integral-center steps with the same controlled continuation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_integral_sequence_of_finite_center_factorization (N : ℕ) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (_hJ : J ≠ ⊥)
      (b : ℕ) (_hb : 0 < b) (I : X.IdealSheafData) (hI : I ≠ ⊥)
      (K : Fin N → X.IdealSheafData),
      (∀ i, K i ≠ ⊥) → (∀ i, IsIntegral (K i).subscheme) →
      (∀ i, Smooth ((K i).subschemeι ≫ f)) →
      (∀ i j, i ≠ j → K i ⊔ K j = ⊤) → I = ∏ i, K i →
      Smooth (I.subschemeι ≫ f) → J ≤ I ^ b →
      ∀ R : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup I hI)
        (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b),
        R.integralCenters → ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, S.integralCenters := by
  induction N with
  | zero =>
      intro X _ _ f _ J hJ b _ I hI K _ _ _ _ hfactor _ _ R hR
      have hi : I = ⊤ := by simpa only [Fin.prod_univ_zero, Scheme.IdealSheafData.one_eq_top] using hfactor
      clear hfactor
      subst I
      let : IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hI) := Global.PrincipalBlowup.Construction.globalBlowupToBase_isIso_of_locallyPrincipal ⊤ hI
        (Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.top X)
      exact R.transport_integral_iso hR f J hJ (asIso (GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hI)) rfl
        (Global.PrincipalBlowup.Construction.globalBlowupControlledIdeal_top_center J hI b).symm
  | succ N ih =>
      intro X _ _ f _ J hJ b hb I hI K hK hInt hSm hDis hfactor hIs hp R hR
      let C := K 0
      let L := ∏ i : Fin N, K i.succ
      have hCL : C ⊔ L = ⊤ := Blowups.Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top C
        (fun i : Fin N => K i.succ) Finset.univ
        (fun i _ => hDis 0 i.succ (Fin.succ_ne_zero i).symm)
      have hL : L ≠ ⊥ := Integral.IdealSheafProducts.Construction.idealSheaf_finset_prod_ne_bot (fun i : Fin N => K i.succ) Finset.univ
        (fun i _ => hK i.succ)
      have hi : I = C * L := hfactor.trans (Fin.prod_univ_succ K)
      clear hfactor
      subst I
      let : Smooth ((C * L).subschemeι ≫ f) := hIs
      let : Smooth (C.subschemeι ≫ f) := hSm 0
      let : Smooth (L.subschemeι ≫ f) := Blowups.Smooth.ComaximalFactor.Construction.smooth_comaximal_right_factor f C L hCL
      let κ := GlobalBlowup.Data.Construction.globalBlowupToBase C (hK 0)
      let L' := L.comap κ
      have hL' : L' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot C L (hK 0) hL
      let : Smooth (κ ≫ f) := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f C (hK 0)
      let J₁ := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J (hK 0) b
      have hJ₁ : J₁ ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot C J (hK 0) b hJ
      have hCp : J ≤ C ^ b := hp.trans (pow_le_pow_left' (show C * L ≤ C from fun _ => Ideal.mul_le_left) b)
      have hLp : J ≤ L ^ b := hp.trans (pow_le_pow_left' (show C * L ≤ L from fun _ => Ideal.mul_le_right) b)
      have hL'p : J₁ ≤ L' ^ b := Disjoint.CenterPermissibility.Construction.globalBlowup_preserves_disjoint_center_permissibility C L J (hK 0) b b
        (by rwa [sup_comm]) hLp
      obtain ⟨R₂, hR₂⟩ := Disjoint.FactorSequenceTransport.Construction.disjointFactor_integral_sequence_transport f C L J (hK 0) hL hJ hCL b hp R hR
      let K' (i : Fin N) := (K i.succ).comap κ
      have hK' (i : Fin N) : K' i ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot C (K i.succ) (hK 0) (hK i.succ)
      have hInt' (i : Fin N) : IsIntegral (K' i).subscheme :=
        @Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_integral _ _ _ C (K i.succ) (hK 0)
          (hDis 0 i.succ (Fin.succ_ne_zero i).symm) (hInt i.succ)
      have hSm' (i : Fin N) : Smooth ((K' i).subschemeι ≫ (κ ≫ f)) :=
        @Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth _ _ _ _ f C (K i.succ) (hK 0)
          (hDis 0 i.succ (Fin.succ_ne_zero i).symm) (hSm i.succ)
      have hDis' (i j : Fin N) (hij : i ≠ j) : K' i ⊔ K' j = ⊤ := by
        change (K i.succ).comap κ ⊔ (K j.succ).comap κ = ⊤
        rw [← Scheme.IdealSheafData.comap_sup, hDis i.succ j.succ
          (fun h => hij (Fin.succ_injective _ h)), Scheme.IdealSheafData.comap_top]
      have hf' : L' = ∏ i, K' i := DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod (fun i : Fin N => K i.succ) Finset.univ κ
      have hs' : Smooth (L'.subschemeι ≫ (κ ≫ f)) := Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth f C L (hK 0) hCL
      obtain ⟨tail, htail⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C (hK 0)) (κ ≫ f) J₁ hJ₁ b hb L' hL'
        K' hK' hInt' hSm' hDis' hf' hs' hL'p R₂ hR₂
      exact ⟨.blowup C (hK 0) hb hCp (hSm 0) inferInstance tail, hInt 0, htail⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CenterFactorSequence.Construction
