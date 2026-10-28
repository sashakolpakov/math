import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CenterFactorSequence

/-! # Disjoint Control Prefix -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointControlPrefix.Construction

noncomputable section

/-! A prescribed finite list of disjoint smooth factors gives an actual prefix isomorphic to the blowup of their union. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_disjoint_control_prefix (N : ℕ) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (b : ℕ), 0 < b →
      ∀ (I : X.IdealSheafData) (hI : I ≠ ⊥) (K : Fin N → X.IdealSheafData),
      (∀ i, K i ≠ ⊥) → (∀ i, Smooth ((K i).subschemeι ≫ f)) →
      (∀ i j, i ≠ j → K i ⊔ K j = ⊤) → I = ∏ i, K i →
      Smooth (I.subschemeι ≫ f) → J ≤ I ^ b →
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g L) (e : Y ≅ GlobalBlowup.Data.Construction.globalBlowup I hI),
        P.followsCenters (List.ofFn K) ∧ P.stepCount = N ∧ e.hom ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI = P.toBase ∧
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap e.hom = L := by
  induction N with
  | zero =>
      intro X _ _ f _ J b _ I hI K _ _ _ hfactor _ _
      have hi : I = ⊤ := by
        simpa only [Fin.prod_univ_zero, Scheme.IdealSheafData.one_eq_top] using hfactor
      clear hfactor
      subst I
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hI
      let : IsIso π := Global.PrincipalBlowup.Construction.globalBlowupToBase_isIso_of_locallyPrincipal ⊤ hI (Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.top X)
      refine ⟨X, f, J, .stop, (asIso π).symm, ?_, rfl, ?_, ?_⟩
      · change List.ofFn K = []
        exact List.ofFn_zero
      · exact IsIso.inv_hom_id π
      · change (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ J hI b).comap (inv π) = J
        rw [Global.PrincipalBlowup.Construction.globalBlowupControlledIdeal_top_center, ← Scheme.IdealSheafData.comap_comp,
          IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  | succ N ih =>
      intro X _ _ f _ J b hb I hI K hK hSm hDis hfactor hIs hp
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
      have hCp : J ≤ C ^ b := hp.trans (pow_le_pow_left' (show C * L ≤ C from fun _ => Ideal.mul_le_left) b)
      have hLp : J ≤ L ^ b := hp.trans (pow_le_pow_left' (show C * L ≤ L from fun _ => Ideal.mul_le_right) b)
      have hL'p : J₁ ≤ L' ^ b := Disjoint.CenterPermissibility.Construction.globalBlowup_preserves_disjoint_center_permissibility C L J (hK 0) b b
        (by rwa [sup_comm]) hLp
      let K' (i : Fin N) := (K i.succ).comap κ
      have hK' (i : Fin N) : K' i ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot C (K i.succ) (hK 0) (hK i.succ)
      have hSm' (i : Fin N) : Smooth ((K' i).subschemeι ≫ (κ ≫ f)) :=
        @Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth _ _ _ _ f C (K i.succ) (hK 0)
          (hDis 0 i.succ (Fin.succ_ne_zero i).symm) (hSm i.succ)
      have hDis' (i j : Fin N) (hij : i ≠ j) : K' i ⊔ K' j = ⊤ := by
        change (K i.succ).comap κ ⊔ (K j.succ).comap κ = ⊤
        rw [← Scheme.IdealSheafData.comap_sup, hDis i.succ j.succ
          (fun h => hij (Fin.succ_injective _ h)), Scheme.IdealSheafData.comap_top]
      have hf' : L' = ∏ i, K' i := DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod (fun i : Fin N => K i.succ) Finset.univ κ
      have hs' : Smooth (L'.subschemeι ≫ (κ ≫ f)) := Blowup.DisjointCenter.Construction.globalBlowup_disjoint_center_smooth f C L (hK 0) hCL
      obtain ⟨Y, g, M, tail, eT, hfollow, hcount, heT, hM⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C (hK 0)) (κ ≫ f) J₁ b hb
        L' hL' K' hK' hSm' hDis' hf' hs' hL'p
      let eD := Disjoint.FactorControlledTransform.Construction.disjointFactorBlowupIso C L (hK 0) hL hCL
      refine ⟨Y, g, M, .blowup C (hK 0) hb hCp (hSm 0) inferInstance tail,
        eT.trans eD, ?_, ?_, ?_, ?_⟩
      · change ∃ rest, List.ofFn K = C :: rest ∧
          tail.followsCenters (rest.map (fun L => L.comap κ))
        refine ⟨List.ofFn (fun i : Fin N => K i.succ), List.ofFn_succ, ?_⟩
        rw [List.map_ofFn]
        exact hfollow
      · change tail.stepCount + 1 = N + 1
        rw [hcount]
      · change (eT.hom ≫ eD.hom) ≫ GlobalBlowup.Data.Construction.globalBlowupToBase (C * L) hI = tail.toBase ≫ κ
        rw [Category.assoc, Disjoint.FactorControlledTransform.Construction.disjointFactorBlowupIso_over, Disjoint.FactorBlowupIso.Construction.disjointFactorBlowupToBase,
          ← Category.assoc, heT]
      · rw [Iso.trans_hom, Scheme.IdealSheafData.comap_comp,
          Disjoint.FactorControlledTransform.Construction.disjointFactorBlowupIso_controlled C L J (hK 0) hL hCL b hp]
        exact hM

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DisjointControlPrefix.Construction
