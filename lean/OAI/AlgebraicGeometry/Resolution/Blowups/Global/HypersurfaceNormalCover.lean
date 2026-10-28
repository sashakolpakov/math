import OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicAffineNormalFrames
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.HypersurfaceNormalFrames
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel

/-! # Hypersurface Normal Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.HypersurfaceNormalCover.Construction

noncomputable section

/-! Smooth contained Cartier hypersurfaces admit native common normal frames near every center point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_hypersurface_normal_neighborhood
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hH : H ≠ ⊥)
    [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      (I.ideal U = ⊤ ∨
        letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
        ∃ (ι : Type) (_ : DecidableEq ι) (g : ι → I.ideal U)
          (D : ι → Derivation ℂ Γ(X, U) Γ(X, U)),
          (∀ i j, D i (g j).val = if i = j then 1 else 0) ∧
          Ideal.span (Set.range (fun i => (g i).val)) = I.ideal U ∧
          ∃ j : ι, H.ideal U = Ideal.span {(g j).val}) := by
  classical
  by_cases hx : x ∈ I.support
  · obtain ⟨U, hxU, z, hz, hHz⟩ := Locally.PrincipalRegular.Construction.locallyPrincipal_regular_generators H hH hlocal x
    let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    let : Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f I U
    let : Algebra.Smooth ℂ (Γ(X, U) ⧸ Ideal.span {z}) := by
      rw [← hHz]
      exact SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f H U
    have hzI : z ∈ I.ideal U := (hHI U) (by rw [hHz]; exact Ideal.mem_span_singleton_self z)
    let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    have hxrange : x ∈ U.2.fromSpec.opensRange := by rw [U.2.opensRange_fromSpec]; exact hxU
    obtain ⟨p, hp⟩ := hxrange
    have hIp : I.ideal U ≤ p.asIdeal := by
      have hm := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) hxU).mp hx
      have hpre : p ∈ U.2.fromSpec ⁻¹' X.zeroLocus (I.ideal U : Set Γ(X, U)) := by
        change U.2.fromSpec p ∈ X.zeroLocus (I.ideal U : Set Γ(X, U))
        rwa [hp]
      rwa [U.2.fromSpec_preimage_zeroLocus] at hpre
    obtain ⟨S, aS, hsS, φ, hopen, q, hq, ι, hι, hdec, v, D, hD, hv, hgen⟩ :=
      Blowups.Smooth.HypersurfaceNormalFrames.Construction.smooth_hypersurface_center_pointed_normal_frame (k := ℂ) (I.ideal U) z hz hzI p hIp
    let : Algebra ℂ S := aS
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hopen
    let j := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.2.fromSpec
    have hg : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S := by
      dsimp only [j]
      rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
      apply congrArg Spec.map
      ext c
      exact φ.commutes c
    have hjq : j q = x := by
      change U.2.fromSpec (PrimeSpectrum.comap φ.toRingHom q) = x
      rw [hq]
      exact hp
    have hIn : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span (Set.range v)) := by
      rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel, hgen]
    have hHn : H.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v none}) := by
      rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel, hHz, Ideal.map_span, Set.image_singleton, hv]
    obtain ⟨V, hxV, g, E, hE, hspan, hnormal⟩ :=
      IntrinsicAffineNormalFrames.Construction.exists_native_affine_normal_frame f I H S j hg q v D hD none hIn hHn
    exact ⟨V, hjq ▸ hxV, Or.inr ⟨Option ι, inferInstance, g, E, hE, hspan, none, hnormal⟩⟩
  · obtain ⟨V, hV, hxV, hVI⟩ := exists_isAffineOpen_mem_and_subset
      (U := I.support.compl) (x := x) hx
    let U : X.affineOpens := ⟨V, hV⟩
    let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    refine ⟨U, hxV, Or.inl ?_⟩
    apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff (I.ideal U) ⊤).mp
    rw [DifferentialUnitGluing.Construction.affineQuotientKernel_top]
    have ht : I.comap U.2.fromSpec = ⊤ := by
      apply ControlledIdealKernel.Construction.idealSheaf_comap_eq_top_of_avoids_support
      intro p hp
      have hm : U.2.fromSpec p ∈ U.1 := by
        have hr : U.2.fromSpec p ∈ U.2.fromSpec.opensRange := ⟨p, rfl⟩
        rwa [U.2.opensRange_fromSpec] at hr
      exact hVI hm hp
    exact (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel I U).symm.trans ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.HypersurfaceNormalCover.Construction
