import OAI.AlgebraicGeometry.Resolution.Blowups.Global.HypersurfaceNormalCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.DerivationHom

/-! # Intrinsic Normal Open Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicNormalOpenRefinement.Construction

noncomputable section

/-! Smooth native normal equations can be retained inside any prescribed ambient open neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineRestriction_etale {X : Scheme} {U V : X.affineOpens} (hVU : V ≤ U) :
    (Blowup.Functor.Construction.affineRestriction hVU).Etale := by
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have he : Spec.map (CommRingCat.ofHom (Blowup.Functor.Construction.affineRestriction hVU)) ≫ U.2.fromSpec = V.2.fromSpec :=
    IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE (X := X.Opens) hVU).op
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Blowup.Functor.Construction.affineRestriction hVU)) ≫ U.2.fromSpec) := by
    rw [he]
    infer_instance
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Blowup.Functor.Construction.affineRestriction hVU))) :=
    IsOpenImmersion.of_comp _ U.2.fromSpec
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (Blowup.Functor.Construction.affineRestriction hVU))).mp inferInstance

theorem exists_native_normal_neighborhood_within
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (H : X.IdealSheafData) (hH : H ≠ ⊥)
    [Smooth (H.subschemeι ≫ f)] (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H)
    (O : X.Opens) (x : X) (hxH : x ∈ H.support) (hxO : x ∈ O) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ O ∧
      ∃ z : Γ(X, V), H.ideal V = Ideal.span {z} ∧
        letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f V
        ∃ N : Derivation ℂ Γ(X, V) Γ(X, V), N z = 1 := by
  obtain ⟨U, hxU, hcase⟩ := Global.HypersurfaceNormalCover.Construction.exists_global_hypersurface_normal_neighborhood f H H hH hlocal le_rfl x
  rcases hcase with hunit | hframe
  · have hm := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := H) hxU).mp hxH
    rw [hunit] at hm
    change x ∈ X.zeroLocus (Set.univ : Set Γ(X, U)) at hm
    rw [Scheme.zeroLocus_univ] at hm
    exact (hm hxU).elim
  · let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    obtain ⟨ι, hdec, g, N, hN, _, i, hnormal⟩ := hframe
    obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset
      (U := U.1 ⊓ O) (x := x) ⟨hxU, hxO⟩
    let V : X.affineOpens := ⟨W, hW⟩
    have hVU : V ≤ U := hsub.trans inf_le_left
    let : Algebra ℂ Γ(X, V) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f V
    let φ := Blowup.Functor.Construction.affineRestriction hVU
    have hφ : φ.Etale := affineRestriction_etale hVU
    have hφk : ∀ c : ℂ, φ (algebraMap ℂ Γ(X, U) c) = algebraMap ℂ Γ(X, V) c :=
      RingHom.congr_fun (Affine.ComplexNaturality.Construction.affineComplexScalars_restrict f hVU)
    let D := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ hφ hφk (N i)
    refine ⟨V, hxW, hsub.trans inf_le_right, φ (g i).val,
      Locally.PrincipalIdealSheaf.Construction.principal_idealSheaf_restrict H hVU (g i).val hnormal, D, ?_⟩
    change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom ℂ φ hφ hφk (N i) (φ (g i).val) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hN, ite_eq_left rfl, map_one]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicNormalOpenRefinement.Construction
